(* Heterogeneous AVL tree, by Jeremy Yallop.
   Used in GADT LR automata *)

type (_, _) ordering =
   LT : (_,  _ ) ordering
 | EQ : ('a, 'a) ordering
 | GT : (_,  _ ) ordering

module type OrderedType =
sig
  type 'a t
  type 'a value
  val compare : 'a t -> 'b t -> ('a, 'b) ordering
end

module type S =
sig
  type _ key
  type _ value
  type t
  val empty : t
  val mem : _ key -> t -> bool
  val add : 'a key -> 'a value -> t -> t
  val find : 'a key -> t -> 'a value option
end

module Make (Ord: OrderedType)
  : S with type 'a key = 'a Ord.t
       and type 'a value = 'a Ord.value
  =
struct
  type 'a key = 'a Ord.t
  type 'a value = 'a Ord.value

  (* Borrowed and adapted from OCaml's standard library.  The OCaml
     license (LGPL version 2 with linking exception) applies. *)
  type t =
      Empty
    | Node : t * 'a key * 'a value * t * int -> t

  let empty = Empty

  let height = function
      Empty -> 0
    | Node(_,_,_,_,h) -> h

  let create : 'a. t -> 'a key -> 'a value -> t -> t =
    fun l x d r ->
      let hl = height l and hr = height r in
      Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

  let bal : 'a. t -> 'a key -> 'a value -> t -> t =
    fun l x d r ->
    let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
    let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
    if hl > hr + 2 then begin
      match l with
        Empty -> invalid_arg "Hmap.bal"
      | Node(ll, lv, ld, lr, _) ->
          if height ll >= height lr then
            create ll lv ld (create lr x d r)
          else begin
            match lr with
              Empty -> invalid_arg "Hmap.bal"
            | Node(lrl, lrv, lrd, lrr, _)->
                create (create ll lv ld lrl) lrv lrd (create lrr x d r)
          end
    end else if hr > hl + 2 then begin
      match r with
        Empty -> invalid_arg "Hmap.bal"
      | Node(rl, rv, rd, rr, _) ->
          if height rr >= height rl then
            create (create l x d rl) rv rd rr
          else begin
            match rl with
              Empty -> invalid_arg "Hmap.bal"
            | Node(rll, rlv, rld, rlr, _) ->
                create (create l x d rll) rlv rld (create rlr rv rd rr)
          end
    end else
      Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))


  let rec add : type a. a key -> a value -> t -> t =
    fun x data -> function
      Empty ->
        Node(Empty, x, data, Empty, 1)
    | Node(l, v, d, r, h) ->
        match Ord.compare x v with
        | EQ ->
          Node(l, x, data, r, h)
        | LT ->
          let ll = add x data l in
          bal ll v d r
        | GT ->
          let rr = add x data r in
          bal l v d rr

  let rec mem : type a. a key -> t -> bool =
   fun x -> function
      Empty ->
        false
    | Node(l, v, d, r, _) ->
        match Ord.compare x v with
        EQ -> true
      | LT -> mem x l
      | GT -> mem x r

  let rec find : type a. a key -> t -> a value option =
    fun x -> function
      Empty ->
        None
    | Node(l, v, d, r, _) ->
        match Ord.compare x v with
          EQ -> Some d
        | LT -> find x l
        | GT -> find x r
end

