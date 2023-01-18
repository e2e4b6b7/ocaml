(* TEST
   * expect
*)

(* romanv e2e4b6b7 *)
let id2 x = match x with `A | `B -> x;;
let el = id2 `A;;
let lst = [( id2 `A ); `C ];;
[%%expect {|
val id2 : ([< `A | `B ] as 'a) -> 'a = <fun>
val el : [< `A | `B > `A ] = `A
Line 3, characters 23-25:
3 | let lst = [( id2 `A ); `C ];;
                           ^^
Error: This expression has type [> `C ]
       but an expression was expected of type [< `A | `B > `A ]
       The second variant type does not allow tag(s) `C
|}]
