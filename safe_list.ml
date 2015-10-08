type ('a,_) t =
  | Nil : ('a, unit) t
  | Cons : 'a * ('a, 'b) t -> ('a, unit -> 'b) t

let rec smap: type l. ('a -> 'b) -> ('a, l) t -> ('b, l) t = fun f -> function
  | Nil -> Nil
  | Cons (h, t) -> Cons (f h, smap f t)
