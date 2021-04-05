module HList = struct
  type (_, _) hlist =
    | Empty : ('a, 'a) hlist
    | (::) : 'c * ('a, 'b) hlist -> ('c -> 'a, 'b) hlist

  let cons : type a b c. c -> (a, b) hlist -> (c -> a, b) hlist =
    fun h tl -> h :: tl

  let hd : type a b c. (c -> a, b) hlist -> c option = function
    | Empty -> None
    | c :: _ -> Some c

  let tl : type a b c. (c -> a, b) hlist -> (a, b) hlist option = function
    | Empty -> None
    | _ :: tl -> Some tl

  type iterf = {
    iter : 'a. 'a -> unit;
  }

  let rec iter : type a b. iterf -> (a, b) hlist -> unit = fun iterf l ->
    match l with
    | Empty -> ()
    | c :: tl -> iterf.iter c; iter iterf tl

  let l = '2' :: "str" :: Empty

  let rec append : type a b c d. (a, b) hlist -> (b, d) hlist -> (a, d) hlist = fun l1 l2 ->
    match l1 with
    | Empty -> l2
    | hd :: tl -> hd :: (append tl l2)
end

