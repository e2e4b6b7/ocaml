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

let id2 x = match x with `A | `B -> x

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
?error?
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

let f y =
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
type t = [`A | `B]
val f : `A | `B | `C -> int = <fun>
val f : T -> int = <fun>
val f : `A | `B -> int = <fun>
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
val f : 'a t -> int = <fun>
val f : 'a t -> int = <fun>
|}]

let f v = (* failing *)
  match v, v with
  | `A, `A -> 4
  | _, `B -> 5
  | _, `A -> 6
