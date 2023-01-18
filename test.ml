(* let f kind nesting =
  match kind, nesting with
  | `S, `Outside -> 0
  | `S, `Inside _ -> 1
  | `E, `Outside -> 2
  | `E, `Inside _ -> 3 *)

type (_, _) eq = Refl : ('a, 'a) eq


let f f' : ('c, 'c) eq -> ('d, 'd) eq = 
  (fun Refl -> let Refl = f' Refl in Refl)
