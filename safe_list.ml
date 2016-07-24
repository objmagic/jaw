type ('a,_) t =
  | Nil : ('a, unit) t
  | Cons : 'a * ('a, 'b) t -> ('a, unit -> 'b) t

let rec smap: type l. ('a -> 'b) -> ('a, l) t -> ('b, l) t = fun f -> function
  | Nil -> Nil
  | Cons (h, t) -> Cons (f h, smap f t)

let rec smap2: type l. ('a -> 'b -> 'c) -> ('a, l) t -> ('b, l) t -> ('c, l) t =
  fun f a b ->
  match b with
  | Nil -> Nil
  | Cons (hb,tb) ->
     let  Cons (ha, ta) = a in Cons (f ha hb , smap2 f ta tb)
