(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Representation of types and declarations *)

open Asttypes

(* Type expressions for the core language *)

type transient_expr =
  { mutable desc: type_desc;
    mutable level: int;
    mutable scope: int;
    id: int }

and type_expr = transient_expr

and type_desc =
    Tvar of string option
  | Tarrow of arg_label * type_expr * type_expr * commutable
  | Ttuple of type_expr list
  | Tconstr of Path.t * type_expr list * abbrev_memo ref
  | Tobject of type_expr * (Path.t * type_expr list) option ref
  | Tfield of string * field_kind * type_expr * type_expr
  | Tnil
  | Tlink of type_expr
  | Tsubst of type_expr * type_expr option
  | Tvariant of row_desc
  | Tunivar of string option
  | Tpoly of type_expr * type_expr list
  | Tpackage of Path.t * (Longident.t * type_expr) list

and set_data =
  | SUnknown of string
  | STags of string * label list
  | SVar of string * int ref
  | STop

and set_variance = Left | Right | Unknown

and row_desc =
    { mutable row_fields: (label * type_expr option) list;
      row_fixed: fixed_explanation option;
      row_name: (Path.t * type_expr list) option;
      set_data: set_data }
and fixed_explanation =
  | Univar of type_expr | Fixed_private | Reified of Path.t | Rigid
and row_field = [`some] row_field_gen
and _ row_field_gen =
    RFpresent : type_expr option -> [> `some] row_field_gen
  | RFeither :
      { no_arg: bool;
        arg_type: type_expr list;
        matched: bool;
        ext: [`some | `none] row_field_gen ref} -> [> `some] row_field_gen
  | RFabsent : [> `some] row_field_gen
  | RFnone : [> `none] row_field_gen

and abbrev_memo =
    Mnil
  | Mcons of private_flag * Path.t * type_expr * type_expr * abbrev_memo
  | Mlink of abbrev_memo ref

and any = [`some | `none | `var]
and field_kind = [`some|`var] field_kind_gen
and _ field_kind_gen =
    FKvar : {mutable field_kind: any field_kind_gen} -> [> `var] field_kind_gen
  | FKprivate : [> `none] field_kind_gen  (* private method; only under FKvar *)
  | FKpublic  : [> `some] field_kind_gen  (* public method *)
  | FKabsent  : [> `some] field_kind_gen  (* hidden private method *)

and commutable = [`some|`var] commutable_gen
and _ commutable_gen =
    Cok      : [> `some] commutable_gen
  | Cunknown : [> `none] commutable_gen
  | Cvar : {mutable commu: any commutable_gen} -> [> `var] commutable_gen

module TransientTypeOps = struct
  type t = type_expr
  let compare t1 t2 = t1.id - t2.id
  let hash t = t.id
  let equal t1 t2 = t1 == t2
end

(* *)

module Uid = Shape.Uid

(* Maps of methods and instance variables *)

module MethSet = Misc.Stdlib.String.Set
module VarSet = Misc.Stdlib.String.Set

module Meths = Misc.Stdlib.String.Map
module Vars = Misc.Stdlib.String.Map


(* Value descriptions *)

type value_description =
  { val_type: type_expr;                (* Type of the value *)
    val_kind: value_kind;
    val_loc: Location.t;
    val_attributes: Parsetree.attributes;
    val_uid: Uid.t;
  }

and value_kind =
    Val_reg                             (* Regular value *)
  | Val_prim of Primitive.description   (* Primitive *)
  | Val_ivar of mutable_flag * string   (* Instance variable (mutable ?) *)
  | Val_self of
      class_signature * self_meths * Ident.t Vars.t * string
                                        (* Self *)
  | Val_anc of class_signature * Ident.t Meths.t * string
                                        (* Ancestor *)

and self_meths =
  | Self_concrete of Ident.t Meths.t
  | Self_virtual of Ident.t Meths.t ref

and class_signature =
  { csig_self: type_expr;
    mutable csig_self_row: type_expr;
    mutable csig_vars: (mutable_flag * virtual_flag * type_expr) Vars.t;
    mutable csig_meths: (method_privacy * virtual_flag * type_expr) Meths.t; }

and method_privacy =
  | Mpublic
  | Mprivate of field_kind

(* Variance *)

module Variance = struct
  type t = int
  type f = May_pos | May_neg | May_weak | Inj | Pos | Neg | Inv
  let single = function
    | May_pos -> 1
    | May_neg -> 2
    | May_weak -> 4
    | Inj -> 8
    | Pos -> 16
    | Neg -> 32
    | Inv -> 64
  let union v1 v2 = v1 lor v2
  let inter v1 v2 = v1 land v2
  let subset v1 v2 = (v1 land v2 = v1)
  let eq (v1 : t) v2 = (v1 = v2)
  let set x b v =
    if b then v lor single x else  v land (lnot (single x))
  let mem x = subset (single x)
  let null = 0
  let unknown = 7
  let full = 127
  let covariant = single May_pos lor single Pos lor single Inj
  let swap f1 f2 v =
    let v' = set f1 (mem f2 v) v in set f2 (mem f1 v) v'
  let conjugate v = swap May_pos May_neg (swap Pos Neg v)
  let get_upper v = (mem May_pos v, mem May_neg v)
  let get_lower v = (mem Pos v, mem Neg v, mem Inv v, mem Inj v)
  let unknown_signature ~injective ~arity =
    let v = if injective then set Inj true unknown else unknown in
    Misc.replicate_list v arity
end

module Separability = struct
  type t = Ind | Sep | Deepsep
  type signature = t list
  let eq (m1 : t) m2 = (m1 = m2)
  let rank = function
    | Ind -> 0
    | Sep -> 1
    | Deepsep -> 2
  let compare m1 m2 = compare (rank m1) (rank m2)
  let max m1 m2 = if rank m1 >= rank m2 then m1 else m2

  let print ppf = function
    | Ind -> Format.fprintf ppf "Ind"
    | Sep -> Format.fprintf ppf "Sep"
    | Deepsep -> Format.fprintf ppf "Deepsep"

  let print_signature ppf modes =
    let pp_sep ppf () = Format.fprintf ppf ",@," in
    Format.fprintf ppf "@[(%a)@]"
      (Format.pp_print_list ~pp_sep print) modes

  let default_signature ~arity =
    let default_mode = if Config.flat_float_array then Deepsep else Ind in
    Misc.replicate_list default_mode arity
end

(* Type definitions *)

type type_declaration =
  { type_params: type_expr list;
    type_arity: int;
    type_kind: type_decl_kind;
    type_private: private_flag;
    type_manifest: type_expr option;
    type_variance: Variance.t list;
    type_separability: Separability.t list;
    type_is_newtype: bool;
    type_expansion_scope: int;
    type_loc: Location.t;
    type_attributes: Parsetree.attributes;
    type_immediate: Type_immediacy.t;
    type_unboxed_default: bool;
    type_uid: Uid.t;
 }

and type_decl_kind = (label_declaration, constructor_declaration) type_kind

and ('lbl, 'cstr) type_kind =
    Type_abstract
  | Type_record of 'lbl list * record_representation
  | Type_variant of 'cstr list * variant_representation
  | Type_open

and record_representation =
    Record_regular                      (* All fields are boxed / tagged *)
  | Record_float                        (* All fields are floats *)
  | Record_unboxed of bool    (* Unboxed single-field record, inlined or not *)
  | Record_inlined of int               (* Inlined record *)
  | Record_extension of Path.t          (* Inlined record under extension *)

and variant_representation =
    Variant_regular          (* Constant or boxed constructors *)
  | Variant_unboxed          (* One unboxed single-field constructor *)

and label_declaration =
  {
    ld_id: Ident.t;
    ld_mutable: mutable_flag;
    ld_type: type_expr;
    ld_loc: Location.t;
    ld_attributes: Parsetree.attributes;
    ld_uid: Uid.t;
  }

and constructor_declaration =
  {
    cd_id: Ident.t;
    cd_args: constructor_arguments;
    cd_res: type_expr option;
    cd_loc: Location.t;
    cd_attributes: Parsetree.attributes;
    cd_uid: Uid.t;
  }

and constructor_arguments =
  | Cstr_tuple of type_expr list
  | Cstr_record of label_declaration list

type extension_constructor =
  { ext_type_path: Path.t;
    ext_type_params: type_expr list;
    ext_args: constructor_arguments;
    ext_ret_type: type_expr option;
    ext_private: private_flag;
    ext_loc: Location.t;
    ext_attributes: Parsetree.attributes;
    ext_uid: Uid.t;
  }

and type_transparence =
    Type_public      (* unrestricted expansion *)
  | Type_new         (* "new" type *)
  | Type_private     (* private type *)

(* Type expressions for the class language *)

type class_type =
    Cty_constr of Path.t * type_expr list * class_type
  | Cty_signature of class_signature
  | Cty_arrow of arg_label * type_expr * class_type

type class_declaration =
  { cty_params: type_expr list;
    mutable cty_type: class_type;
    cty_path: Path.t;
    cty_new: type_expr option;
    cty_variance: Variance.t list;
    cty_loc: Location.t;
    cty_attributes: Parsetree.attributes;
    cty_uid: Uid.t;
 }

type class_type_declaration =
  { clty_params: type_expr list;
    clty_type: class_type;
    clty_path: Path.t;
    clty_variance: Variance.t list;
    clty_loc: Location.t;
    clty_attributes: Parsetree.attributes;
    clty_uid: Uid.t;
  }

(* Type expressions for the module language *)

type visibility =
  | Exported
  | Hidden

type module_type =
    Mty_ident of Path.t
  | Mty_signature of signature
  | Mty_functor of functor_parameter * module_type
  | Mty_alias of Path.t

and functor_parameter =
  | Unit
  | Named of Ident.t option * module_type

and module_presence =
  | Mp_present
  | Mp_absent

and signature = signature_item list

and signature_item =
    Sig_value of Ident.t * value_description * visibility
  | Sig_type of Ident.t * type_declaration * rec_status * visibility
  | Sig_typext of Ident.t * extension_constructor * ext_status * visibility
  | Sig_module of
      Ident.t * module_presence * module_declaration * rec_status * visibility
  | Sig_modtype of Ident.t * modtype_declaration * visibility
  | Sig_class of Ident.t * class_declaration * rec_status * visibility
  | Sig_class_type of Ident.t * class_type_declaration * rec_status * visibility

and module_declaration =
  {
    md_type: module_type;
    md_attributes: Parsetree.attributes;
    md_loc: Location.t;
    md_uid: Uid.t;
  }

and modtype_declaration =
  {
    mtd_type: module_type option;  (* Note: abstract *)
    mtd_attributes: Parsetree.attributes;
    mtd_loc: Location.t;
    mtd_uid: Uid.t;
  }

and rec_status =
    Trec_not                   (* first in a nonrecursive group *)
  | Trec_first                 (* first in a recursive group *)
  | Trec_next                  (* not first in a recursive/nonrecursive group *)

and ext_status =
    Text_first                     (* first constructor of an extension *)
  | Text_next                      (* not first constructor of an extension *)
  | Text_exception                 (* an exception *)


(* Constructor and record label descriptions inserted held in typing
   environments *)

type constructor_description =
  { cstr_name: string;                  (* Constructor name *)
    cstr_res: type_expr;                (* Type of the result *)
    cstr_existentials: type_expr list;  (* list of existentials *)
    cstr_args: type_expr list;          (* Type of the arguments *)
    cstr_arity: int;                    (* Number of arguments *)
    cstr_tag: constructor_tag;          (* Tag for heap blocks *)
    cstr_consts: int;                   (* Number of constant constructors *)
    cstr_nonconsts: int;                (* Number of non-const constructors *)
    cstr_generalized: bool;             (* Constrained return type? *)
    cstr_private: private_flag;         (* Read-only constructor? *)
    cstr_loc: Location.t;
    cstr_attributes: Parsetree.attributes;
    cstr_inlined: type_declaration option;
    cstr_uid: Uid.t;
   }

and constructor_tag =
    Cstr_constant of int                (* Constant constructor (an int) *)
  | Cstr_block of int                   (* Regular constructor (a block) *)
  | Cstr_unboxed                        (* Constructor of an unboxed type *)
  | Cstr_extension of Path.t * bool     (* Extension constructor
                                           true if a constant false if a block*)

let equal_tag t1 t2 =
  match (t1, t2) with
  | Cstr_constant i1, Cstr_constant i2 -> i2 = i1
  | Cstr_block i1, Cstr_block i2 -> i2 = i1
  | Cstr_unboxed, Cstr_unboxed -> true
  | Cstr_extension (path1, b1), Cstr_extension (path2, b2) ->
      Path.same path1 path2 && b1 = b2
  | (Cstr_constant _|Cstr_block _|Cstr_unboxed|Cstr_extension _), _ -> false

let may_equal_constr c1 c2 =
  c1.cstr_arity = c2.cstr_arity
  && (match c1.cstr_tag,c2.cstr_tag with
     | Cstr_extension _,Cstr_extension _ ->
         (* extension constructors may be rebindings of each other *)
         true
     | tag1, tag2 ->
         equal_tag tag1 tag2)

let item_visibility = function
  | Sig_value (_, _, vis)
  | Sig_type (_, _, _, vis)
  | Sig_typext (_, _, _, vis)
  | Sig_module (_, _, _, _, vis)
  | Sig_modtype (_, _, vis)
  | Sig_class (_, _, _, vis)
  | Sig_class_type (_, _, _, vis) -> vis

type label_description =
  { lbl_name: string;                   (* Short name *)
    lbl_res: type_expr;                 (* Type of the result *)
    lbl_arg: type_expr;                 (* Type of the argument *)
    lbl_mut: mutable_flag;              (* Is this a mutable field? *)
    lbl_pos: int;                       (* Position in block *)
    lbl_all: label_description array;   (* All the labels in this type *)
    lbl_repres: record_representation;  (* Representation for this record *)
    lbl_private: private_flag;          (* Read-only field? *)
    lbl_loc: Location.t;
    lbl_attributes: Parsetree.attributes;
    lbl_uid: Uid.t;
   }

let rec bound_value_identifiers = function
    [] -> []
  | Sig_value(id, {val_kind = Val_reg}, _) :: rem ->
      id :: bound_value_identifiers rem
  | Sig_typext(id, _, _, _) :: rem -> id :: bound_value_identifiers rem
  | Sig_module(id, Mp_present, _, _, _) :: rem ->
      id :: bound_value_identifiers rem
  | Sig_class(id, _, _, _) :: rem -> id :: bound_value_identifiers rem
  | _ :: rem -> bound_value_identifiers rem

let signature_item_id = function
  | Sig_value (id, _, _)
  | Sig_type (id, _, _, _)
  | Sig_typext (id, _, _, _)
  | Sig_module (id, _, _, _, _)
  | Sig_modtype (id, _, _)
  | Sig_class (id, _, _, _)
  | Sig_class_type (id, _, _, _)
    -> id

(**** Definitions for backtracking ****)

type change =
    Ctype of type_expr * type_desc
  | Ccompress of type_expr * type_desc * type_desc
  | Clevel of type_expr * int
  | Cscope of type_expr * int
  | Cname of
      (Path.t * type_expr list) option ref * (Path.t * type_expr list) option
  | Crow of [`none|`some] row_field_gen ref
  | Ckind of [`var] field_kind_gen
  | Ccommu of [`var] commutable_gen
  | Cuniv of type_expr option ref * type_expr option

type changes =
    Change of change * changes ref
  | Unchanged
  | Invalid

let trail = Local_store.s_table ref Unchanged

let log_change ch =
  let r' = ref Unchanged in
  !trail := Change (ch, r');
  trail := r'

(* constructor and accessors for [field_kind] *)

type field_kind_view =
    Fprivate
  | Fpublic
  | Fabsent

let rec field_kind_internal_repr : field_kind -> field_kind = function
  | FKvar {field_kind = FKvar _ | FKpublic | FKabsent as fk} ->
      field_kind_internal_repr fk
  | kind -> kind

let field_kind_repr fk =
  match field_kind_internal_repr fk with
  | FKvar _ -> Fprivate
  | FKpublic -> Fpublic
  | FKabsent -> Fabsent

let field_public = FKpublic
let field_absent = FKabsent
let field_private () = FKvar {field_kind=FKprivate}

(* Constructor and accessors for [commutable] *)

let rec is_commu_ok : type a. a commutable_gen -> bool = function
  | Cvar {commu} -> is_commu_ok commu
  | Cunknown -> false
  | Cok -> true

let commu_ok = Cok
let commu_var () = Cvar {commu=Cunknown}

(**** Representative of a type ****)

let rec repr_link (t : type_expr) d : type_expr -> type_expr =
 function
   {desc = Tlink t' as d'} ->
     repr_link t d' t'
 | {desc = Tfield (_, k, _, t') as d'}
   when field_kind_internal_repr k = FKabsent ->
     repr_link t d' t'
 | t' ->
     log_change (Ccompress (t, t.desc, d));
     t.desc <- d;
     t'

let repr_link1 t = function
   {desc = Tlink t' as d'} ->
     repr_link t d' t'
 | {desc = Tfield (_, k, _, t') as d'}
   when field_kind_internal_repr k = FKabsent ->
     repr_link t d' t'
 | t' -> t'

let repr t =
  match t.desc with
   Tlink t' ->
     repr_link1 t t'
 | Tfield (_, k, _, t') when field_kind_internal_repr k = FKabsent ->
     repr_link1 t t'
 | _ -> t

(* getters for type_expr *)

let get_desc t = (repr t).desc
let get_level t = (repr t).level
let get_scope t = (repr t).scope
let get_id t = (repr t).id

(* transient type_expr *)

module Transient_expr = struct
  let create desc ~level ~scope ~id = {desc; level; scope; id}
  let set_desc ty d = ty.desc <- d
  let set_stub_desc ty d = assert (ty.desc = Tvar None); ty.desc <- d
  let set_level ty lv = ty.level <- lv
  let set_scope ty sc = ty.scope <- sc
  let coerce ty = ty
  let repr = repr
  let type_expr ty = ty
end

(* Comparison for [type_expr]; cannot be used for functors *)

let eq_type t1 t2 = t1 == t2 || repr t1 == repr t2
let compare_type t1 t2 = compare (get_id t1) (get_id t2)

(* Constructor and accessors for [row_desc] *)

type set_solution =
  | SSSolution of
      string list option * (* lb *)
      string list option   (* ub *)
  | SSFail

module Hashtbl = Hashtbl.Make(struct
  type t = int ref
  let equal = (==)
  let hash = Hashtbl.hash
end)


let constraints = ref []
let edges_cache = ref None

let is_not_test = false

let file =
  if is_not_test then Stdlib.stdout else
  let file = open_out_gen [Open_append; Open_creat] 0o666 "dump.txt" in
  Printf.fprintf file "\n-- New env --\n\n";
  file

let copies = ref []
let trace_copies id =
  let rec trace_copies_aux copies id =
    match copies with
    | [] -> "", id
    | (from_id, to_id) :: copies ->
        if to_id == id
        then
          let trace, init_id = trace_copies_aux copies from_id in
          Printf.sprintf "%d <- %s" !id trace, init_id
        else trace_copies_aux copies id in
  let trace, id = trace_copies_aux !copies id in
  if String.length trace > 0 then
  Printf.fprintf file "%s%d\n" trace !id

let sprint_set_data set_data = match set_data with
  | SUnknown from -> Printf.sprintf "Unknown from %s" from
  | SVar (from, id) ->
      trace_copies id;
      Printf.sprintf "V from %s: %d" from !id
  | STags (from, tags) ->
      Printf.sprintf "Tags from %s: %s"
        from
        (String.concat "" ["[";String.concat "," tags;"]"])
  | STop -> "T"

and sprint_variance v = match v with
  | Left -> "Left"
  | Right -> "Right"
  | Unknown -> "Unknown"

let set_constraint from ?(v = Right) s1 s2 =
  if is_not_test then () else
  (Printf.fprintf file "From: %s; Variance: %s\n" from (sprint_variance v);
  Printf.fprintf file "%s -- %s\n\n" (sprint_set_data s1) (sprint_set_data s2);
  flush file;
  edges_cache := None;
  constraints := match v with
  | Right -> (s1, s2) :: !constraints
  | Left -> (s2, s1) :: !constraints
  | Unknown -> (s1, s2) :: (s2, s1) :: !constraints)

let set_unknown_constraint from =
  if is_not_test then () else
  Printf.fprintf file "Unknown constraint from: %s\n" from; flush file

let cur_id = ref 0
let new_id () = cur_id := !cur_id + 1; ref !cur_id

let set_id set_data = match set_data with
  | SVar (_, id) -> id
  | _ -> ref (-1)
let row_set_id row = !(set_id row.set_data)

let mk_set_top () =
  if is_not_test then SUnknown "Not in test" else
  STop
let mk_set_unknown from =
  if is_not_test then SUnknown "Not in test" else begin
  Printf.fprintf file "Unknown from %s" from;
  flush file;
  SUnknown from
  end
let mk_set_var from =
  if is_not_test then SUnknown "Not in test" else
  SVar (from, new_id ())
let mk_set_var_tags from tags =
  if is_not_test then SUnknown "Not in test" else
  (let var = mk_set_var from in
  let desc = Printf.sprintf "mk_set_var_tags: %s" from in
  set_constraint desc (STags (from, tags)) var;
  var)
let mk_set_tags from tags =
  if is_not_test then SUnknown "Not in test" else
  STags (from, tags)
let row_set_data row =
  if is_not_test then SUnknown "Not in test" else
  row.set_data
let cp_set_variable from id =
  let new_id = new_id () in

  copies := (id, new_id) :: !copies;

  (* let with_id sd =
    match sd with
    | SVar (_, idd) -> id == idd
    | _ -> false
  in
  let with_id (sd1, sd2) = with_id sd1 || with_id sd2 in

  let cp_constraints = List.filter with_id !constraints in
  let replace_id sd =
    match sd with
    | SVar (_, idd) as v -> if id == idd then SVar (from, new_id) else v
    | sd -> sd
  in
  let replace_id (sd1, sd2) = (replace_id sd1, replace_id sd2) in
  let cp_constraints = List.map replace_id cp_constraints in
  constraints := List.append cp_constraints !constraints;
  edges_cache := None; *)

  SVar (from, new_id)

let cp_set_data from row =
  if is_not_test then SUnknown "Not in test" else
  match row.set_data with
  | SVar (_, id) -> cp_set_variable from id
  | sd -> sd

let sprint_tags tags = String.concat "" ["[";String.concat "," tags;"]"]

let intersect_lists l1 l2 = List.filter (fun x -> List.memq x l1) l2
let intersect_lists_assoc l1 l2 = List.filter (fun (x, _) -> List.memq x l1) l2
(* Checks that l1 is subset of l2 *)
let subset_lists l1 l2 = List.for_all (fun id -> List.memq id l2) l1

(* edges = ((edges_var_ub, edges_tag_ub), (edges_var_lb, edges_tag_lb)) *)

let rec uniq l =
  match l with
  | [] -> []
  | h :: t -> h :: uniq (List.filter (fun e -> not (e == h)) t)

let used_ids constraints =
  let app s l =
    match s with
    | SVar (_, id) -> id :: l
    | _ -> l
  in
  let used_ids =
    List.fold_left
      (fun l (s1, s2) -> app s1 @@ app s2 l)
      []
      constraints
  in
  uniq used_ids

exception Romanv of string

let collect_edges_ () = try
  let constraints = !constraints in
  let used_ids = used_ids constraints in

  let edges_var_ub = Hashtbl.create 13 in
  let edges_tag_ub = Hashtbl.create 13 in
  let edges_var_lb = Hashtbl.create 13 in
  let edges_tag_lb = Hashtbl.create 13 in
  List.iter
    (fun id ->
      Hashtbl.add edges_var_ub id (ref []);
      Hashtbl.add edges_var_lb id (ref []);
      Hashtbl.add edges_tag_lb id (ref []))
    used_ids;
  List.iter
    (fun (sd1, sd2) ->
      (match sd2 with
      | SVar (_, id2) ->
          (match sd1 with
          | STags (_, tags) ->
              let t = Hashtbl.find edges_tag_lb id2 in
              t := List.append tags !t
          | SVar (_, id1) ->
              let v = Hashtbl.find edges_var_lb id2 in
              v := id1 :: !v
          | _ -> ())
      | _ -> ());

      (match sd1 with
      | SVar (_, id1) ->
          (match sd2 with
          | STags (_, tags) ->
              let t = Hashtbl.find_opt edges_tag_ub id1 in
              (match t with
              | Some t -> t := intersect_lists tags !t
              | None -> Hashtbl.add edges_tag_ub id1 (ref tags))
          | SVar (_, id2) ->
              let v = Hashtbl.find edges_var_ub id1 in
              v := id2 :: !v
          | _ -> ())
      |  _ -> ()))
    constraints;
  List.iter
    (fun id ->
      match Hashtbl.find_opt edges_tag_ub id with
      | Some _ -> ()
      | None -> Hashtbl.add edges_tag_ub id (ref []))
    used_ids;
  used_ids, ((edges_var_ub, edges_tag_ub), (edges_var_lb, edges_tag_lb))
with Not_found -> raise (Romanv "Not_found in collect_edges_")

let collect_edges () =
  let (_, edges) = collect_edges_ () in
  edges_cache := Some edges; edges

let id_used id =
  let used_ids = used_ids !constraints in
  List.memq id used_ids

let solve_for_ merge (edges_var, edges_tag) id =
  if not (Hashtbl.mem edges_tag id) ||
     not (Hashtbl.mem edges_var id)
  then None else try
    let used = Hashtbl.create 17 in
    let rec solve_for_aux id =
      Hashtbl.add used id ();
      let v = Hashtbl.find edges_var id in
      let sub_vars = List.filter (fun id -> not @@ Hashtbl.mem used id) !v in
      let t = Hashtbl.find edges_tag id in
      let t = !t in
      let t = if t = [] then None else Some t in
      let tags = t :: List.map solve_for_aux sub_vars in
      let tags = List.fold_left merge None tags in
      Option.map (List.sort_uniq String.compare) tags in
    solve_for_aux id
  with Not_found -> raise (Romanv "Not_found in solve_for")

let find_parent id =
  let rec find_parent_aux copies id =
    match copies with
    | [] -> None
    | (from_id, to_id) :: copies ->
      if to_id == id
      then Some from_id
      else find_parent_aux copies id in
  find_parent_aux !copies id

let rec solve_for merge edges id =
  let parent_id = find_parent id in
  match parent_id with
  | Some parent_id ->
      let parent_solution = solve_for merge edges parent_id in
      let solution = solve_for_ merge edges id in
      merge parent_solution solution
  | None -> solve_for_ merge edges id

let solve_ub edges_ub id =
  let opt_intersect a b =
    match a, b with
    | None, None -> None
    | Some t, None | None, Some t -> Some t
    | Some t1, Some t2 -> Some (intersect_lists t1 t2)
  in
  solve_for opt_intersect edges_ub id

let solve_lb edges_lb id =
  let opt_merge a b =
    match a, b with
    | None, None -> None
    | Some t, None | None, Some t -> Some t
    | Some t1, Some t2 -> Some (List.append t1 t2)
  in
  solve_for opt_merge edges_lb id

let log_bounds ub lb id =
  let sprint_bound b = match b with
  | Some t -> sprint_tags t
  | None -> "-" in
  trace_copies id;
  Printf.fprintf file "%d: ub: %s | lb: %s\n\n" !id (sprint_bound ub) (sprint_bound lb)

let solve_set_type (edges_ub, edges_lb) id =
  assert (id_used id);
  let ub = solve_ub edges_ub id in
  let lb = solve_lb edges_lb id in

  log_bounds ub lb id;

  match ub, lb with
  | Some ub_tags, Some lb_tags ->
          if subset_lists lb_tags ub_tags
            then SSSolution (Some lb_tags, Some ub_tags)
            else SSFail
  | Some ub_tags, None -> SSSolution (None, Some ub_tags)
  | None, Some lb_tags -> SSSolution (Some lb_tags, None)
  | None, None -> SSSolution (None, None)

let solve_constraints id =
  let edges = collect_edges () in
  solve_set_type edges id

let print_bound b = match b with
| Some tags -> sprint_tags tags
| None -> "T"

let sprint_set_type row =
  let data = row.set_data in
  match data with
  | STags (from, tags) -> Printf.sprintf "%s: %s" from (sprint_tags tags)
  | SVar (from, id) when id_used id ->
      let solution = solve_constraints id in
      Printf.sprintf "%d, %s: %s" !id from (match solution with
      | SSSolution (lb, ub) ->
          Printf.sprintf "[< %s > %s]" (print_bound lb) (print_bound ub)
      | SSFail -> "Fail")
  | SVar (from, _) ->
      Printf.sprintf "Unsure from %s: %s" from
        (sprint_tags (List.map fst row.row_fields))
  | SUnknown from -> Printf.sprintf "Unknown from %s" from
  | STop -> "T"

let create_row ~set_data ~fields ~fixed ~name =
    { row_fields=fields; row_fixed=fixed;
      row_name=name; set_data=set_data }

(* [row_fields] subsumes the original [row_repr] *)
let row_fields row =
  match row.set_data with
  | SVar (_, id) when id_used id ->
      let (edges, _) = collect_edges () in
      let fields = row.row_fields in
      let ub = solve_ub edges id in
      (match ub with
      | Some tags -> intersect_lists_assoc tags fields
      | None -> fields)
  | SUnknown _ | SVar _ -> row.row_fields
  | STags (_, tags) -> intersect_lists_assoc tags row.row_fields
  | STop -> row.row_fields

let row_fields_lb row =
  match row.set_data with
  | SVar (_, id) when id_used id ->
      let (_, edges) = collect_edges () in
      let fields = row.row_fields in
      let lb = solve_lb edges id in
      (match lb with
      | Some tags -> intersect_lists_assoc tags fields
      | None -> fields)
  | SUnknown _ | SVar _ -> row.row_fields
  | _ -> assert false

let row_repr_no_fields row = row

let row_fixed row = (row_repr_no_fields row).row_fixed
let row_name row = (row_repr_no_fields row).row_name

let row_closed row =
  match row.set_data with
  | SVar (_, id) when id_used id ->
      let (edges, _) = collect_edges () in
      let ub = solve_ub edges id in
      (match ub with
      | Some _ -> true
      | None -> false)
  | SUnknown _ | SVar _ -> false
  | _ -> assert false

let dump tag row =
  Printf.fprintf file "get_row_field dump\n";
  match row.row_name with
  | Some (path, _) ->
      Printf.fprintf file "Name: %s\n" (Path.name path)
  | None -> ();
  Printf.fprintf file "Tags: %s\n" (sprint_tags (List.map fst row.row_fields));
  Printf.fprintf file "Inferred tags: %s\n" (sprint_set_type row);
  Printf.fprintf file "Searching for tag: %s\n" tag

let get_row_field_ tag row =
  let rec find = function
    | (tag',f) :: fields ->
        if tag = tag' then Some f else find fields
    | [] -> None
  in find row.row_fields

let get_row_field ?d tag row =
  match d with
  | Some true ->
      let a = get_row_field_ tag row in
      if a == None then dump tag row;
      a
  | _ -> get_row_field_ tag row


let set_row_fields row fields =
  row.row_fields <- fields

let set_row_name row row_name =
  let row_fields = row_fields row in
  let row = row_repr_no_fields row in
  {row with row_fields; row_name}

type row_desc_repr =
    Row of { fields: (label * type_expr option) list;
             closed:bool;
             fixed:fixed_explanation option;
             name:(Path.t * type_expr list) option }

let row_repr row =
  let fields = row_fields row in
  let row = row_repr_no_fields row in
  let closed = row_closed row in
  Row { fields;
        closed;
        fixed = row.row_fixed;
        name = row.row_name }

type row_field_view =
    Rpresent of type_expr option
  | Reither of bool * type_expr list * bool
        (* 1st true denotes a constant constructor *)
        (* 2nd true denotes a tag in a pattern matching, and
           is erased later *)
  | Rabsent

let rec row_field_repr_aux tl : row_field -> row_field = function
  | RFeither ({ext = {contents = RFnone}} as r) ->
      RFeither {r with arg_type = tl@r.arg_type}
  | RFeither {arg_type;
              ext = {contents = RFeither _ | RFpresent _ | RFabsent as rf}} ->
      row_field_repr_aux (tl@arg_type) rf
  | RFpresent (Some _) when tl <> [] ->
      RFpresent (Some (List.hd tl))
  | RFpresent _ as rf -> rf
  | RFabsent -> RFabsent

let row_field_repr fi =
  match row_field_repr_aux [] fi with
  | RFeither {no_arg; arg_type; matched} -> Reither (no_arg, arg_type, matched)
  | RFpresent t -> Rpresent t
  | RFabsent -> Rabsent

let rec row_field_ext (fi : row_field) =
  match fi with
  | RFeither {ext = {contents = RFnone} as ext} -> ext
  | RFeither {ext = {contents = RFeither _ | RFpresent _ | RFabsent as rf}} ->
      row_field_ext rf
  | _ -> Misc.fatal_error "Types.row_field_ext "

let rf_present oty = RFpresent oty
let rf_absent = RFabsent
let rf_either ?use_ext_of ~no_arg arg_type ~matched =
  let ext =
    match use_ext_of with
      Some rf -> row_field_ext rf
    | None -> ref RFnone
  in
  RFeither {no_arg; arg_type; matched; ext}

let rf_either_of = function
  | None ->
      RFeither {no_arg=true; arg_type=[]; matched=false; ext=ref RFnone}
  | Some ty ->
      RFeither {no_arg=false; arg_type=[ty]; matched=false; ext=ref RFnone}

let eq_row_field_ext rf1 rf2 =
  row_field_ext rf1 == row_field_ext rf2

let changed_row_field_exts l f =
  let exts = List.map row_field_ext l in
  f ();
  List.exists (fun r -> !r <> RFnone) exts

let match_row_field ~present ~absent ~either (f : row_field) =
  match f with
  | RFabsent -> absent ()
  | RFpresent t -> present t
  | RFeither {no_arg; arg_type; matched; ext} ->
      let e : row_field option =
        match !ext with
        | RFnone -> None
        | RFeither _ | RFpresent _ | RFabsent as e -> Some e
      in
      either no_arg arg_type matched e


(**** Some type creators ****)

let new_id = Local_store.s_ref (-1)

let create_expr = Transient_expr.create

let newty3 ~level ~scope desc  =
  incr new_id;
  create_expr desc ~level ~scope ~id:!new_id

let newty2 ~level desc =
  newty3 ~level ~scope:Ident.lowest_scope desc

                  (**********************************)
                  (*  Utilities for backtracking    *)
                  (**********************************)

let undo_change = function
    Ctype  (ty, desc) -> Transient_expr.set_desc ty desc
  | Ccompress (ty, desc, _) -> Transient_expr.set_desc ty desc
  | Clevel (ty, level) -> Transient_expr.set_level ty level
  | Cscope (ty, scope) -> Transient_expr.set_scope ty scope
  | Cname  (r, v)    -> r := v
  | Crow   r         -> r := RFnone
  | Ckind  (FKvar r) -> r.field_kind <- FKprivate
  | Ccommu (Cvar r)  -> r.commu <- Cunknown
  | Cuniv  (r, v)    -> r := v

type snapshot = changes ref * int
let last_snapshot = Local_store.s_ref 0

let log_type ty =
  if ty.id <= !last_snapshot then log_change (Ctype (ty, ty.desc))
let link_type_ ty ty' =
  log_type ty;
  let desc = ty.desc in
  Transient_expr.set_desc ty (Tlink ty');
  (* Name is a user-supplied name for this unification variable (obtained
   * through a type annotation for instance). *)
  match desc, ty'.desc with
    Tvar name, Tvar name' ->
      begin match name, name' with
      | Some _, None -> log_type ty'; Transient_expr.set_desc ty' (Tvar name)
      | None, Some _ -> ()
      | Some _, Some _ ->
          if ty.level < ty'.level then
            (log_type ty'; Transient_expr.set_desc ty' (Tvar name))
      | None, None   -> ()
      end
  | _ -> ()
  (* ; assert (check_memorized_abbrevs ()) *)
  (*  ; check_expans [] ty' *)

let link_type ty ty' =
  let ty = repr ty in
  let ty' = repr ty' in
  if ty == ty' then () else
  match ty.desc, ty'.desc with
  | Tvariant _, Tvariant _ -> ()
  | _ -> link_type_ ty ty'
(* TODO: consider eliminating set_type_desc, replacing it with link types *)
let set_type_desc ty td =
  let ty = repr ty in
  if td != ty.desc then begin
    log_type ty;
    Transient_expr.set_desc ty td
  end
(* TODO: separate set_level into two specific functions: *)
(*  set_lower_level and set_generic_level *)
let set_level ty level =
  let ty = repr ty in
  if level <> ty.level then begin
    if ty.id <= !last_snapshot then log_change (Clevel (ty, ty.level));
    Transient_expr.set_level ty level
  end
(* TODO: introduce a guard and rename it to set_higher_scope? *)
let set_scope ty scope =
  let ty = repr ty in
  if scope <> ty.scope then begin
    if ty.id <= !last_snapshot then log_change (Cscope (ty, ty.scope));
    Transient_expr.set_scope ty scope
  end
let set_univar rty ty =
  log_change (Cuniv (rty, !rty)); rty := Some ty
let set_name nm v =
  log_change (Cname (nm, !nm)); nm := v

let rec link_row_field_ext ~(inside : row_field) (v : row_field) =
  match inside with
  | RFeither {ext = {contents = RFnone} as e} ->
      let RFeither _ | RFpresent _ | RFabsent as v = v in
      log_change (Crow e); e := v
  | RFeither {ext = {contents = RFeither _ | RFpresent _ | RFabsent as rf}} ->
      link_row_field_ext ~inside:rf v
  | _ -> invalid_arg "Types.link_row_field_ext"

let rec link_kind ~(inside : field_kind) (k : field_kind) =
  match inside with
  | FKvar ({field_kind = FKprivate} as rk) as inside ->
      (* prevent a loop by normalizing k and comparing it with inside *)
      let FKvar _ | FKpublic | FKabsent as k = field_kind_internal_repr k in
      if k != inside then begin
        log_change (Ckind inside);
        rk.field_kind <- k
      end
  | FKvar {field_kind = FKvar _ | FKpublic | FKabsent as inside} ->
      link_kind ~inside k
  | _ -> invalid_arg "Types.link_kind"

let rec commu_repr : commutable -> commutable = function
  | Cvar {commu = Cvar _ | Cok as commu} -> commu_repr commu
  | c -> c

let rec link_commu ~(inside : commutable) (c : commutable) =
  match inside with
  | Cvar ({commu = Cunknown} as rc) as inside ->
      (* prevent a loop by normalizing c and comparing it with inside *)
      let Cvar _ | Cok as c = commu_repr c in
      if c != inside then begin
        log_change (Ccommu inside);
        rc.commu <- c
      end
  | Cvar {commu = Cvar _ | Cok as inside} ->
      link_commu ~inside c
  | _ -> invalid_arg "Types.link_commu"

let set_commu_ok c = link_commu ~inside:c Cok

let snapshot () =
  let old = !last_snapshot in
  last_snapshot := !new_id;
  (!trail, old)

let rec rev_log accu = function
    Unchanged -> accu
  | Invalid -> assert false
  | Change (ch, next) ->
      let d = !next in
      next := Invalid;
      rev_log (ch::accu) d

let backtrack ~cleanup_abbrev (changes, old) =
  match !changes with
    Unchanged -> last_snapshot := old
  | Invalid -> failwith "Types.backtrack"
  | Change _ as change ->
      cleanup_abbrev ();
      let backlog = rev_log [] change in
      List.iter undo_change backlog;
      changes := Unchanged;
      last_snapshot := old;
      trail := changes

let undo_first_change_after (changes, _) =
  match !changes with
  | Change (ch, _) ->
      undo_change ch
  | _ -> ()

let rec rev_compress_log log r =
  match !r with
    Unchanged | Invalid ->
      log
  | Change (Ccompress _, next) ->
      rev_compress_log (r::log) next
  | Change (_, next) ->
      rev_compress_log log next

let undo_compress (changes, _old) =
  match !changes with
    Unchanged
  | Invalid -> ()
  | Change _ ->
      let log = rev_compress_log [] changes in
      List.iter
        (fun r -> match !r with
          Change (Ccompress (ty, desc, d), next) when ty.desc == d ->
            Transient_expr.set_desc ty desc; r := !next
        | _ -> ())
        log
