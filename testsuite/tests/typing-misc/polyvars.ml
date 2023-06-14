(* TEST
   * expect
*)

let c = `C;;
[%%expect {|
val c : `C = `C
|}]


let lst = [`A; `C];;
[%%expect {|
val lst : `A | `C list = [`A; `C]
|}]

let f x = match x with `A -> `B

let b = f `A;;
[%%expect {|
val f : `A -> `B = <fun>
val b : `B = `B
|}]

let f x = match x with `A 1 -> `B "one" | `A _ -> `C ();;
[%%expect {|
val f : `A of int -> `B of string | `C of unit = <fun>
|}]

let id2 x = match x with `A | `B -> x (* prinitng fails *)

let a = id2 `A

let lst = [( id2 `A ); `C ];;
[%%expect {|
val id2 : (`A | `B as 'a) -> 'a = <fun>
val a : `A = `A
val lst : `A | `C list = [`A; `C]
|}]

let f y =
   match y with
   | `A -> `C
   | `B -> `D

let err = f `C;;
[%%expect {|
val f : `A | `B -> `C | `D = <fun>
Line 6, characters 12-14:
6 | let err = f `C;;
                ^^
Error: This expression has type Bot but an expression was expected of type
         Bot
       These two variant types have no intersection
|}]

let f y =
   match y with
   | `A -> `C
   | y -> y

let d = f `D;;
[%%expect {|
val f : (T as 'a) -> `C | 'a = <fun>
val d : `C | `D = `D
|}]

let f y = (* failing *)
   match y with
   | `B :: _ -> `C
   | `C :: _ -> List.hd y
   | [] -> `B;;
[%%expect {|
val f : `B | `C list -> `B | `C = <fun>
|}]

let f x =
   match x with
   | `B -> [`C]
   | `A -> [x];;
[%%expect {|
val f : (`A | `B as 'a) -> `C | 'a list = <fun>
|}]

let f f1 f2 e = f1 e || f2 e || f1 `A || f2 `B;; (* failing *)
[%%expect {|
val f : (`A | 'a -> bool) -> (`B | 'a -> bool) -> 'a -> bool = <fun>
|}]

type t = [`A | `B]

let f x =
   match x with
   | `C -> 1
   | #t -> 2

let f v =
   match v with
   | `C -> 1
   | #t -> 2
   | _ -> 3

let f x =
   match x with
   | #t -> assert false;;
[%%expect {|
type t = `A | `B
val f : `A | `B | `C -> int = <fun>
val f : T -> int = <fun>
val f : `A | `B -> 'a = <fun>
|}]

type 'a t = {
   field: 'a;
}

let f v =
  match v.field with
  | `A -> 4
  | `B -> 5

let f v =
  match v with
  | {field = `A} -> 4
  | {field = `B} -> 5;;
[%%expect {|
type 'a t = { field : 'a; }
val f : `A | `B t -> int = <fun>
val f : `A | `B t -> int = <fun>
|}]

let f v =
  match v, v with
  | `A, `A -> 4
  | _, `B -> 5
  | _, `A -> 6
[%%expect {|
val f : `A | `B -> int = <fun>
|}]

let f v =
  (match v with
  | `A -> 4
  | _ -> 5) +
  (match v with
  | `A -> 1
  | `B -> 2)
[%%expect {|
val f : `A | `B -> int = <fun>
|}]

type ab = [ `A | `B ];;
let f (x : [`A]) = match x with #ab -> 1;;
[%%expect{|
type ab = `A | `B
val f : `A -> int = <fun>
|}];;

let f x = ignore (match x with #ab -> 1); ignore (x : [`A]);;
[%%expect{|
val f : `A -> unit = <fun>
|}];;

let f x = ignore (match x with `A|`B -> 1); ignore (x : [`A]);;
[%%expect{|
val f : `A -> unit = <fun>
|}];;

let f (x : [< `A | `B]) = match x with `A | `B | `C -> 0;;
[%%expect{|
Line 1, characters 49-51:
1 | let f (x : [< `A | `B]) = match x with `A | `B | `C -> 0;; (* warn *)
                                                     ^^
Warning 12 [redundant-subpat]: this sub-pattern is unused.
val f : `A | `B -> int = <fun>
|}];;

let f (x : [`A | `B]) = match x with `A | `B | `C -> 0;;
[%%expect{|
Line 1, characters 49-51:
1 | let f (x : [< `A | `B]) = match x with `A | `B | `C -> 0;; (* warn *)
                                                     ^^
Warning 12 [redundant-subpat]: this sub-pattern is unused.
val f : `A | `B -> int = <fun>
|}];;

(* imported from in poly.ml *)
type t = A | B;;
function `A,_ -> 1 | _,A -> 2 | _,B -> 3;;
function `A,_ -> 1 | _,(A|B) -> 2;;
function Some `A, _ -> 1 | Some _, A -> 2 | None, A -> 3 | _, B -> 4;;
function Some `A, A -> 1 | Some `A, B -> 1
       | Some _, A -> 2  | None, A -> 3 | _, B -> 4;;
function A, `A -> 1 | A, `B -> 2 | B, _ -> 3;;
function `A, A -> 1 | `B, A -> 2 | _, B -> 3;;
function (`A|`B), _ -> 0 | _,(`A|`B) -> 1;;
function `B,1 -> 1 | _,1 -> 2;;
function 1,`B -> 1 | 1,_ -> 2;;
[%%expect {|
type t = A | B
- : T * t -> int = <fun>
- : T * t -> int = <fun>
- : T option * t -> int = <fun>
- : T option * t -> int = <fun>
- : t * `A | `B -> int = <fun>
- : `A | `B * t -> int = <fun>
Line 9, characters 0-41:
9 | function (`A|`B), _ -> 0 | _,(`A|`B) -> 1;;
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
Here is an example of a case that is not matched:
(`AnyOtherTag, `AnyOtherTag)
- : T * T -> int = <fun>
Line 10, characters 0-29:
10 | function `B,1 -> 1 | _,1 -> 2;;
     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
Here is an example of a case that is not matched:
(_, 0)
Line 10, characters 21-24:
10 | function `B,1 -> 1 | _,1 -> 2;;
                          ^^^
Warning 11 [redundant-case]: this match case is unused.
- : `B * int -> int = <fun>
Line 11, characters 0-29:
11 | function 1,`B -> 1 | 1,_ -> 2;;
     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
Here is an example of a case that is not matched:
(0, _)
Line 11, characters 21-24:
11 | function 1,`B -> 1 | 1,_ -> 2;;
                          ^^^
Warning 11 [redundant-case]: this match case is unused.
- : int * `B -> int = <fun>
|}];;

(* PR#6787 *)
let revapply x f = f x;;

let f x (g : [< `Foo]) =
  let y = `Bar x, g in
  revapply y (fun ((`Bar i), _) -> i);;
(* f : 'a -> [< `Foo ] -> 'a *)
[%%expect{|
val revapply : 'a -> ('a -> 'b) -> 'b = <fun>
val f : 'a -> `Foo -> 'a = <fun>
|}];;

(* PR#6124 *)
let f : ([`A | `B ] as 'a) -> [> 'a] -> unit = fun x (y : [> 'a]) -> ();;
let f (x : [`A | `B] as 'a) (y : [> 'a]) = ();;
[%%expect{|
Line 1, characters 61-63:
1 | let f : ([`A | `B ] as 'a) -> [> 'a] -> unit = fun x (y : [> 'a]) -> ();;
                                                                 ^^
Error: The type 'a does not expand to a polymorphic variant type
Hint: Did you mean `a?
|}]

let f = function `AnyOtherTag, _ -> 1 | _, (`AnyOtherTag|`AnyOtherTag') -> 2;;
[%%expect{|
Line 1, characters 8-76:
1 | let f = function `AnyOtherTag, _ -> 1 | _, (`AnyOtherTag|`AnyOtherTag') -> 2;;
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
Here is an example of a case that is not matched:
(`AnyOtherTag', `AnyOtherTag'')
val f : T * T -> int = <fun>
|}]

let x:(([`A] as 'a)* ([`B] as 'a)) = [`A]
[%%expect {|
Line 1, characters 22-32:
1 | let x:(([`A] as 'a)* ([`B] as 'a)) = [`A]
                          ^^^^^^^^^^
Error: This alias is bound to type Bot but is used as an instance of type Bot
       These two variant types have no intersection
|}]

(** Check that the non-regularity error message is robust to permutation *)

type ('a,'b,'c,'d,'e) a = [ `A of ('d,'a,'e,'c,'b) b ]
and  ('a,'b,'c,'d,'e) b = [ `B of ('c,'d,'e,'a,'b) c ]
and  ('a,'b,'c,'d,'e) c = [ `C of ('a,'b,'c,'d,'e) a ]
[%%expect {|
Line 3, characters 0-54:
3 | type ('a,'b,'c,'d,'e) a = [ `A of ('d,'a,'e,'c,'b) b ]
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This recursive type is not regular.
       The type constructor a is defined as
         type ('a, 'b, 'c, 'd, 'e) a
       but it is used as
         ('e, 'c, 'b, 'd, 'a) a
       after the following expansion(s):
         ('d, 'a, 'e, 'c, 'b) b = `B of ('e, 'c, 'b, 'd, 'a) c,
         ('e, 'c, 'b, 'd, 'a) c = `C of ('e, 'c, 'b, 'd, 'a) a
       All uses need to match the definition for the recursive type to be regular.
|}]

(* PR 10762 *)
type a = int
type t = [ `A of a ]
let inspect: [< t ] -> unit = function
  | `A 0 -> ()
  | `A _ -> ()
[%%expect {|
type a = int
type t = `A of a
val inspect : `A of a -> unit = <fun>
|}]

(* romanv: regression *)

let f a b =
  match a, b with
  | `S, `Outside
  | `S, `Inside -> assert false
  
