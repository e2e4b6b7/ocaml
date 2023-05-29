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

and constraint_relation = Left | Right | Equal | Unknown

and 'a dsf =
  | DsfLink of 'a dsf ref
  | DsfValue of 'a

and row_kind = (label * type_expr option) list

and row_desc =
    { row_kind: row_kind dsf;
      row_fixed: fixed_explanation option;
      row_name: (Path.t * type_expr list) option;
      row_var: type_expr;
      debug_info: (string (* from *) * int (* debug id *)) }
and fixed_explanation =
  | Univar of type_expr | Fixed_private | Reified of Path.t | Rigid

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

(*** Global subtyping constraints ***)

let polyvariants_tag_ub_constraints : (row_desc * label list) list ref = ref []
let polyvariants_tag_lb_constraints : (row_desc * label list) list ref = ref []
let polyvariants_constraints : (row_desc * row_desc) list ref = ref []
let variables_constraints : (type_expr * type_expr) list ref = ref []

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

let rec set_level ty lv = 
  ty.level <- lv;
  List.iter 
    (fun (l, r) -> 
      if l == ty && get_level r != lv then set_level r lv;
      if r == ty && get_level l != lv then set_level l lv)
    !variables_constraints

(* transient type_expr *)

module Transient_expr = struct
  let create desc ~level ~scope ~id = {desc; level; scope; id}
  let set_desc ty d = ty.desc <- d
  let set_stub_desc ty d = assert (ty.desc = Tvar None); ty.desc <- d
  let set_level = set_level
  let set_scope ty sc = ty.scope <- sc
  let coerce ty = ty
  let repr = repr
  let type_expr ty = ty
end

(* Comparison for [type_expr]; cannot be used for functors *)

let eq_type t1 t2 = t1 == t2 || repr t1 == repr t2
let compare_type t1 t2 = compare (get_id t1) (get_id t2)

(* Constructor and accessors for [row_desc] *)

let dsf_init v = DsfLink (ref (DsfValue v))

let rec dsf_get dsf =
  match dsf with
  | DsfLink dsf -> dsf_get !dsf
  | DsfValue v -> v

let rec dsf_last_link dsf =
  match dsf with
  | DsfLink v_ref -> begin
      match !v_ref with
      | DsfLink _ as dsf -> dsf_last_link dsf
      | DsfValue v -> v, v_ref
    end
  | DsfValue _ -> assert false

let dsf_merge f dsf dsf' =
  let v, v_ref = dsf_last_link dsf in
  let v', v_ref' = dsf_last_link dsf' in
  if v_ref == v_ref' then () else
  let v = f v v' in
  let dsf_v = ref (DsfValue v) in
  v_ref := DsfLink dsf_v;
  v_ref' := DsfLink dsf_v;
  assert (dsf_get dsf == dsf_get dsf')

type set_solution =
  | SSUnion of set_solution * set_solution
  | SSIntersection of set_solution * set_solution
  | SSVariable of row_desc
  | SSTags of
      string list option * (* lb *)
      string list option   (* ub *)
  | SSFail

type set_bound_solution = {
  tags: string list option;
  variables: row_desc list;
}

let dump =
  let dump = open_out_gen [Open_append; Open_creat] 0o666 "dump.txt" in
  Printf.fprintf dump "\n-- New env --\n\n";
  dump

let sprint_constraint_relation v = match v with
  | Left -> "Left"
  | Right -> "Right"
  | Equal -> "Equal"
  | Unknown -> "Unknown"

let sprint_tags tags = String.concat "" ["[";String.concat "," tags;"]"]
(* let sprint_row_id {debug_info=(_, id)} = Printf.sprintf "%d" id *)
(* let sprint_row_ids rows = String.concat "," @@ List.map sprint_row_id rows *)

let sprint_row row =
  let (from, id) = row.debug_info in
  Printf.sprintf "Row %d from %s kind %s" id from
    (sprint_tags @@ List.map fst (dsf_get row.row_kind))

let sprint_constrained_ty ty =
  match get_desc ty with
  | Tvariant row -> sprint_row row
  | Tvar _ -> "TVar"
  | _ -> assert false

module RowDescHtbl = Hashtbl.Make(struct
  type t = row_desc
  let equal = (==)
  let hash = Hashtbl.hash
end)

let _add_constraint relation v1 v2 constraints =
  let add ((l, r) as c) cs =
    if List.exists (fun (l', r') -> l' == l && r' == r) cs
      then cs
      else c :: cs
  in
  constraints := match relation with
  | Right -> add (v1, v2) !constraints
  | Left -> add (v2, v1) !constraints
  | Equal | Unknown -> add (v1, v2) @@ add (v2, v1) !constraints

let log_new_polyvariant_constraint from relation row1 row2 =
  Printf.fprintf dump "From: %s; Variance: %s\n" from (sprint_constraint_relation relation);
  Printf.fprintf dump "%s -- %s\n\n" (sprint_row row1) (sprint_row row2);
  flush dump

let add_polyvariant_constraint ?(from="Unknown source") relation row1 row2 =
  log_new_polyvariant_constraint from relation row1 row2;
  _add_constraint relation row1 row2 polyvariants_constraints;
  _add_constraint relation row1.row_var row2.row_var variables_constraints

let log_new_polyvariant_tags_constraint relation row1 tags =
  Printf.fprintf dump "Variance: %s\n" (sprint_constraint_relation relation);
  Printf.fprintf dump "%s -- %s\n\n" (sprint_row row1) (sprint_tags tags);
  flush dump

let add_polyvariant_tags_constrint relation row tags =
  log_new_polyvariant_tags_constraint relation row tags;
  begin
    match relation with
    | Left | Equal | Unknown -> polyvariants_tag_lb_constraints := (row, tags) :: !polyvariants_tag_lb_constraints
    | Right -> ()
  end;
  begin
    match relation with
    | Right | Equal | Unknown -> polyvariants_tag_ub_constraints := (row, tags) :: !polyvariants_tag_ub_constraints
    | Left -> ()
  end

let log_new_constraint from relation ty1 ty2 =
  Printf.fprintf dump "From: %s; Variance: %s\n" from (sprint_constraint_relation relation);
  Printf.fprintf dump "%s -- %s\n\n" (sprint_constrained_ty ty1) (sprint_constrained_ty ty2);
  flush dump

let check_new_constraint ty1 ty2 =
  match get_desc ty1, get_desc ty2 with
  | Tvar _, Tvar _ -> ()
  | Tvariant _, Tvariant _ -> assert false
  | _ -> assert false

let add_constraint ?(from="Unknown source") relation ty1 ty2 =
  log_new_constraint from relation ty1 ty2;
  check_new_constraint ty1 ty2;
  _add_constraint relation ty1 ty2 variables_constraints

let get_imediate_subtypes row =
  List.map fst @@ List.filter (fun (_, r) -> r == row) !polyvariants_constraints

let get_imediate_uptypes row =
  List.map snd @@ List.filter (fun (r, _) -> r == row) !polyvariants_constraints

let rec uniq l =
  match l with
  | [] -> []
  | h :: t -> h :: uniq (List.filter (fun e -> not (e == h)) t)

let merge_lists_compare cmp l1 l2 = List.sort_uniq cmp @@ List.append l1 l2
let intersect_lists l1 l2 = List.filter (fun x -> List.mem x l1) l2
(* let intersect_lists_assoc l1 l2 = List.filter (fun (x, _) -> List.mem x l1) l2 *)
(* Checks that l1 is subset of l2 *)
let subset_lists l1 l2 = List.for_all (fun id -> List.mem id l2) l1
let exclude_listsq l1 l2 = List.filter (fun id -> not @@ List.memq id l2) l1

type row_kind_id = row_kind dsf ref
type row_kind_class = row_kind dsf

(* let sprint_htbl pref htbl kp pv =
  Printf.fprintf dump "Htbl %s:\n" pref;
  RowDescHtbl.iter (fun k v -> Printf.fprintf dump "%s: %s\n" (kp k) (pv v)) htbl;
  Printf.fprintf dump "\n";
  flush stdout *)

(** edges = ((edges_var_ub, edges_tag_ub), (edges_var_lb, edges_tag_lb)) *)

let collect_tag_edges constraints merge =
  let edges_tag = RowDescHtbl.create 13 in
  List.iter
    (fun (row, tags) ->
      match RowDescHtbl.find_opt edges_tag row with
      | None -> RowDescHtbl.add edges_tag row tags
      | Some tags' -> RowDescHtbl.replace edges_tag row (merge tags tags'))
    constraints;
  RowDescHtbl.filter_map_inplace
    (fun _row tags -> Some (uniq tags))
    edges_tag;
  edges_tag

let merge_tags_ub = intersect_lists
let merge_tags_lb = merge_lists_compare String.compare

let collect_tag_ub_edges () =
  collect_tag_edges !polyvariants_tag_ub_constraints merge_tags_ub

let collect_tag_lb_edges () =
  collect_tag_edges !polyvariants_tag_lb_constraints merge_tags_lb

let collect_var_edges () =
  let constraints = !polyvariants_constraints in
  let edges_var_ub = RowDescHtbl.create 13 in
  let edges_var_lb = RowDescHtbl.create 13 in
  let add_constraint htbl row1 row2 =
    match RowDescHtbl.find_opt htbl row1 with
    | None -> RowDescHtbl.add htbl row1 [row2]
    | Some rows -> RowDescHtbl.replace htbl row1 (row2 :: rows) in
  List.iter
    (fun (row1, row2) ->
      add_constraint edges_var_ub row1 row2;
      add_constraint edges_var_lb row2 row1)
    constraints;
  edges_var_ub, edges_var_lb

let collect_edges () =
  let (edges_var_ub, edges_var_lb) = collect_var_edges () in
  let edges_tag_ub = collect_tag_ub_edges () in
  let edges_tag_lb = collect_tag_lb_edges () in
  ((edges_var_ub, edges_tag_ub),(edges_var_lb, edges_tag_lb))

let _iter_reachables f edges row =
  let visited = RowDescHtbl.create 17 in
  let rec calc_reachable row =
    if RowDescHtbl.mem visited row then () else begin
    RowDescHtbl.add visited row ();
    f row;
    match RowDescHtbl.find_opt edges row with
    | None -> ()
    | Some direct -> List.iter calc_reachable direct
    end
  in
  calc_reachable row

let find_reachables ((edges, _), (edges', _)) row =
  let reachable = RowDescHtbl.create 17 in
  let add row = RowDescHtbl.add reachable row () in
  _iter_reachables add edges row;
  _iter_reachables add edges' row;
  reachable

(* romanv: Maybe we can merge this components in single type for performance *)
let find_components ((edges, _), _) =
  let reachable = RowDescHtbl.create 17 in
  let rec calc_reachable visited id =
    if RowDescHtbl.mem visited id then () else begin
    RowDescHtbl.add visited id ();
    match RowDescHtbl.find_opt edges id with
    | None -> ()
    | Some direct -> List.iter (calc_reachable visited) direct
    end
  in
  RowDescHtbl.iter
    (fun id _ ->
      let visited = RowDescHtbl.create 17 in
      calc_reachable visited id;
      let visited = RowDescHtbl.fold (fun id _ acc -> id :: acc) visited [] in
      RowDescHtbl.add reachable id visited)
    edges;
  let connected = RowDescHtbl.create 17 in
  RowDescHtbl.iter (fun id1 reachable1 ->
    List.iter (fun id2 ->
      if not (id1 == id2) then
        let reachable2 = RowDescHtbl.find_opt reachable id2 in
        let reachable2 = Option.value reachable2 ~default:[] in
        if List.memq id1 reachable2 then
          match RowDescHtbl.find_opt connected id1 with
          | None -> RowDescHtbl.add connected id1 (ref [id2])
          | Some prev -> prev :=  id2 :: !prev)
    reachable1)
  reachable;
  let connected' = RowDescHtbl.create 17 in
  RowDescHtbl.iter (fun row ref_lst -> RowDescHtbl.add connected' row !ref_lst) connected;
  connected'

let transform_edges_ f edges connected =
  let transformed = RowDescHtbl.create 17 in
  RowDescHtbl.iter
    (fun row con ->
        if not (RowDescHtbl.mem transformed row) then begin
          assert (not (List.memq row con));
          let group = row :: con in
          (* let get_edges row =
            Option.value (RowDescHtbl.find_opt edges row) ~default:[] in
          let group_edges = f get_edges group in *)
          let upd = f group edges in
          List.iter upd group;
          List.iter (fun row -> RowDescHtbl.add transformed row ()) group
        end)
    connected;
  edges

let transform_edges_v =
  transform_edges_
    (fun group edges ->
      let get_edges row = Option.value (RowDescHtbl.find_opt edges row) ~default:[] in
      let new_edges = exclude_listsq (uniq (List.concat_map get_edges group)) group in
      if new_edges = []
      then fun row -> RowDescHtbl.remove edges row
      else fun row -> RowDescHtbl.replace edges row new_edges)

let transform_edges_t_ub =
  transform_edges_
    (fun group edges ->
      let new_edges = List.filter_map (RowDescHtbl.find_opt edges) group in
      match new_edges with
        | [] ->
            fun row -> RowDescHtbl.remove edges row
        | h :: t ->
            let new_edges = List.fold_left merge_tags_ub h t in
            fun row -> RowDescHtbl.replace edges row new_edges)

let transform_edges_t_lb =
  transform_edges_
    (fun group edges ->
      let new_edges = List.filter_map (RowDescHtbl.find_opt edges) group in
      match new_edges with
        | [] ->
            fun row -> RowDescHtbl.remove edges row
        | h :: t ->
            let new_edges = List.fold_left merge_tags_lb h t in
            if new_edges = []
              then fun row -> RowDescHtbl.remove edges row
              else fun row -> RowDescHtbl.replace edges row new_edges)

let transform_edges
  ((edges_ub_vars, edges_ub_tags), (edges_lb_vars, edges_lb_tags)) connected =
  (transform_edges_v edges_ub_vars connected,
   transform_edges_t_ub edges_ub_tags connected),
  (transform_edges_v edges_lb_vars connected,
   transform_edges_t_lb edges_lb_tags connected)

let transform_context context connected =
  let equal row = Option.value (RowDescHtbl.find_opt connected row) ~default:[] in
  let new_context = List.concat @@ List.map equal context in
  uniq @@ List.append context new_context

let solve_for_with_context_ solve_rec merge (edges_var, edges_tag) row =
  let vars_solution =
    let vars_bound = RowDescHtbl.find_opt edges_var row in
    let vars_bound = Option.value vars_bound ~default:[] in
    List.map solve_rec vars_bound in
  let tags_solution =
    let tags = RowDescHtbl.find_opt edges_tag row in
    { tags; variables = [] }
  in
  List.fold_left merge tags_solution vars_solution

let rec solve_for_with_context context merge edges row : set_bound_solution =
  if List.memq row context
  then
    { tags = None; variables = [row] }
  else
    let solve_rec = solve_for_with_context context merge edges in
    solve_for_with_context_ solve_rec merge edges row

let solve_bound_with_context tags_merge context edges row =
  let variables_merge old_variables new_variables =
    uniq @@ List.append old_variables new_variables in
  let solutions_merge
    {tags = old_tags; variables = old_variables}
    {tags = new_tags; variables = new_variables} =
    let tags = tags_merge old_tags new_tags in
    let variables = variables_merge old_variables new_variables in
    {tags; variables}
  in
  solve_for_with_context context solutions_merge edges row

let solve_ub_with_context context edges_ub row =
  let tags_merge old_tags new_tags =
    match old_tags, new_tags with
    | None, None -> None
    | Some t, None | None, Some t -> Some t
    | Some t1, Some t2 -> Some (intersect_lists t1 t2) in
  solve_bound_with_context tags_merge context edges_ub row

let solve_lb_with_context context edges_lb row =
  let tags_merge old_tags new_tags =
    match old_tags, new_tags with
    | None, None -> None
    | Some t, None | None, Some t -> Some t
    | Some t1, Some t2 -> Some (List.append t1 t2) in
  solve_bound_with_context tags_merge context edges_lb row

let solve_set_type_with_context_ context (edges_ub, edges_lb) (row : row_desc) =
  if List.memq row context then SSVariable row else begin

  let {tags=ub_tags; variables=ub_variables} = solve_ub_with_context context edges_ub row in
  let {tags=lb_tags; variables=lb_variables} = solve_lb_with_context context edges_lb row in

  match ub_tags, lb_tags with
  | Some ub_tags, Some lb_tags when not @@ subset_lists lb_tags ub_tags ->
      Printf.fprintf dump "FAIL: %s; %s\n" (sprint_tags ub_tags) (sprint_tags lb_tags);
      flush dump;
      SSFail
  | _ ->
      let solution = SSTags (lb_tags, ub_tags) in
      let solution =
        List.fold_left
          (fun solution var -> SSUnion (solution, SSVariable var))
          solution
          lb_variables in
      let solution =
        List.fold_left
          (fun solution var -> SSIntersection (solution, SSVariable var))
          solution
          ub_variables in
      solution
  end

let filter_edges ((e1,e2),(e3,e4)) reachable =
  let filter htbl =
    RowDescHtbl.filter_map_inplace
      (fun row con ->
        if RowDescHtbl.mem reachable row then Some con else None)
      htbl in
  filter e1;
  filter e2;
  filter e3;
  filter e4

let solve_set_type_with_context context row =
  let edges = collect_edges () in
  let reachable = find_reachables edges row in
  filter_edges edges reachable;
  let connected = find_components edges in
  let edges = transform_edges edges connected in
  let context = transform_context context connected in
  let ans = solve_set_type_with_context_ context edges row in
  ans

(* romanv: Could be solved much faster in case of empty context *)
let solve_set_type row =
  match solve_set_type_with_context [] row with
  | SSTags (lb, ub) ->
      Printf.fprintf dump "SOLVED %s\n" (sprint_row row);
      let lb' = Option.value (Option.map sprint_tags lb) ~default:"-" in
      let ub' = Option.value (Option.map sprint_tags ub) ~default:"-" in
      Printf.fprintf dump "lb: %s\nub: %s\n\n" lb' ub';
      Some (lb, ub)
  | SSFail -> None
  | _ -> assert false

let cp_rows (rows : (row_desc * row_desc) list) : unit =
  List.iter
    (fun (from_row, to_row) ->
      let (_, from_id) = from_row.debug_info in
      let (_, to_id) = to_row.debug_info in
      Printf.fprintf dump "COPY: %d -> %d\n" from_id to_id)
    rows;
  let context = List.map fst rows in
  let solve (from, _to) =
    let context = List.filter (fun row -> not (row == from)) context in
    solve_set_type_with_context context from in
  let solutions = List.map solve rows in
  let rec cp_constraints (from, to_) solution =
    let re = cp_constraints (from, to_) in
    match solution with
    | SSFail -> assert false
    | SSIntersection (solution, SSVariable row) ->
        let row = List.assq row rows in
        add_polyvariant_constraint ~from:"cp_rows" Right to_ row;
        re solution
    | SSUnion (solution, SSVariable row) ->
        let row = List.assq row rows in
        add_polyvariant_constraint ~from:"cp_rows" Left to_ row;
        re solution
    | SSTags (lb, ub) ->
        Option.iter (add_polyvariant_tags_constrint Left to_) lb;
        Option.iter (add_polyvariant_tags_constrint Right to_) ub
    | SSVariable row ->
        add_polyvariant_constraint ~from:"cp_rows" Equal to_ row
    | _ -> assert false
  in
  List.iter2 cp_constraints rows solutions

let cur_id = ref 0
let new_id () = cur_id := !cur_id + 1; !cur_id

let create_row ~from ~var ~kind ~fixed ~name : row_desc =
  let debug_info = (from, new_id ()) in
  { row_kind=dsf_init kind; row_fixed=fixed;
    row_name=name; row_var=var; debug_info }

(* [row_fields] subsumes the original [row_repr] *)
let row_fields_ub row =
  match solve_set_type row with
  | Some (_, Some tags) -> Some (List.map (
      fun tag -> tag,
        let oty = List.assoc_opt tag (dsf_get row.row_kind) in
        match oty with
        | Some ty -> ty
        | None ->
          Printf.fprintf dump "tag %s not found in row %s\n" tag (sprint_row row); flush dump; assert false
      ) tags)
  | Some (_, None) -> None
  | None -> Some []

let row_fields_lb row =
  match solve_set_type row with
  | Some (Some tags, _) -> List.map (fun tag -> tag, List.assoc tag (dsf_get row.row_kind)) tags
  | Some (None, _) | None -> []

let row_kind row = dsf_get row.row_kind
let row_kind_id row = let (_, id) = dsf_last_link row.row_kind in id
let row_kind_class row = row.row_kind
let row_fixed row = row.row_fixed
let row_name row = row.row_name
let row_debug_info row = row.debug_info
let row_var row = row.row_var

let row_closed row =
  match solve_set_type row with
  | Some (_, Some _) -> true
  | Some (_, None) -> false
  | None -> true

let get_row_field tag row =
  List.assoc_opt tag (dsf_get row.row_kind)

let merge_row_kinds f row row' =
  dsf_merge f row.row_kind row'.row_kind

let merge_row_kinds_classes f kind_class kind_class' =
  dsf_merge f kind_class kind_class'

let set_row_name row row_name =
  { row with row_name }

type row_desc_repr =
    Row of { kind:row_kind;
             closed:bool;
             fixed:fixed_explanation option;
             name:(Path.t * type_expr list) option }

let row_repr row =
  let closed = row_closed row in
  Row { kind = dsf_get row.row_kind;
        closed;
        fixed = row.row_fixed;
        name = row.row_name }

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
  | Ckind  (FKvar r) -> r.field_kind <- FKprivate
  | Ccommu (Cvar r)  -> r.commu <- Cunknown
  | Cuniv  (r, v)    -> r := v

type snapshot = changes ref * int
let last_snapshot = Local_store.s_ref 0

let sprint_desc = function
  | Tarrow _ -> "Tarrow"
  | Tvariant _ -> "Tvariant"
  | Tvar _ -> "Tvar"
  | Tunivar _ -> "Tunivar"
  | Tconstr _ -> "Tconstr"
  | Tfield _ -> "Tfield"
  | Tlink _ -> "Tlink"
  | Tobject _ -> "Tobject"
  | Tpackage _ -> "Tpackage"
  | Tnil -> "Tnil"
  | Ttuple _ -> "Ttuple"
  | Tpoly _ -> "Tpoly"
  | Tsubst _ -> "Tsubst"

let dump_link ty ty' =
  if Sys.file_exists "/dump_link" then
  Printf.fprintf dump "link_type: %s - %s\n" (sprint_desc ty.desc) (sprint_desc ty'.desc)

let log_type ty =
  if ty.id <= !last_snapshot then log_change (Ctype (ty, ty.desc))
let link_type ty ty' =
  let ty = repr ty in
  let ty' = repr ty' in
  if ty == ty' then () else begin
  log_type ty;
  dump_link ty ty';
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
  end
  (* ; assert (check_memorized_abbrevs ()) *)
  (*  ; check_expans [] ty' *)(* TODO: consider eliminating set_type_desc, replacing it with link types *)
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
