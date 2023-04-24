(* TEST
   * expect
*)

(* let f x = match x with `A -> `B;; *)

(* let ff y =
   match y with
   | `B :: _ -> `C
   | `C :: _ -> List.hd y
   | [] -> `B;; *)

let id2 x = match x with `A | `B -> x;;

let lst = [id2 `A; `C];;

let f1 y =
   match y with
   | `A -> `C
   | `B -> `D

let f2 y =
   match y with
   | `A -> `C
   | y -> y;;

let v1 = f1 `D

let v2 = f2 `D

let f3 = f2

(* let ff' y =
   match y with
   | `B :: _ -> `C
   | _ :: _ -> List.hd y
   | [] -> `B;; *)


(* let f x = match x,x with
| `A, _ -> 1
| _, `A -> 2
| `A, `A -> 2 *)


(* let f1 x = match x with
| `B -> `A
| _ -> `C;;
[%%expect {|
val f1 : !T! [> `B ] -> ![A,C]! [> `A | `C ] = <fun>
|}] *)

(* let f2 x = match x with
| `B -> `A
| x  -> x;;
[%%expect {|
val f2 : (!T! [> `A | `B ] as 'a) -> ?? = <fun>
|}] *)

(* let f21 = f2 `C;;
let f22 = f2 (`C 1);;

let f3 = f2;; *)

(* let f3 x = match x with
| `B -> [`A]
| `A -> [x];;
[%%expect {|
val f3 : (![A,B]! [< `A | `B > `A ] as 'a) -> ?? list = <fun>
|}] *)

(*

let tmp = f1 `C;;
[%%expect {|
|}]


[%%expect {|
|}]

let id22 x = match x with
| `A -> `A
| `B -> `B
[%%expect {|
|}]

let el = id2 `A;;
[%%expect {|
|}]

let lst = [( id2 `A ); `C ];;
[%%expect {|
|}] *)
