(* mainly by def, modified to be easier by me *)
type (_, _) args =
  | Empty : ('a, 'a) args
  | Cons : 'c * ('a, 'b) args -> ('c -> 'a, 'b) args;;

let l = Cons(false, Cons(1, Cons(2, Empty)));;

let f x y z = if x then y else z;;

let rec app : type a b. a -> (a, b) args -> b =
  fun f arg ->
  match arg with
  | Empty -> f
  | Cons(x, xs) -> app (f x) xs;;

let g = app f l

let h = app f (Cons(false, Empty))

let k = app f (Cons(false, Cons(1.2, Empty)))
