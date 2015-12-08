(* mainly by def, modified to be easier by me *)
type (_, _) args =
  | Empty : ('a, 'a) args
  | :: : 'c * ('a, 'b) args -> ('c -> 'a, 'b) args

let l = false :: 1 :: 2 :: Empty

let f x y z = if x then y else z

let rec app : type a b. a -> (a, b) args -> b =
  fun f arg ->
  match arg with
  | Empty -> f
  | x :: xs -> app (f x) xs;;

let g = app f l

let h = app f (false :: Empty)

let k = app f (false :: 1.2 :: Empty)
