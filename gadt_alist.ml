(** type equality witness *)
module Eq = struct
  type (_, _) t = Refl : ('a, 'a) t
end

module type KV = sig
  type 'a key
  type 'a value
  val equal : 'a key -> 'b key -> ('a, 'b) Eq.t option
end

module type AList = sig
  type 'a key
  type 'a value
  type t
  val empty : t
  val add : 'a key -> 'a value -> t -> t
end

module AssociationList (T : KV) : AList = struct
  
  include T

  type t =
    | Nil : t
    | Cons : 'a key * 'a value * t -> t

  let empty = Nil

  let add k v t = Cons (k, v, t)

  let cast : type a b. (a, b) Eq.t -> a value -> b value = fun Eq.Refl x -> x

  let rec find : type a. a key -> t -> a value option = fun k l ->
    match l with
    | Nil -> None
    | Cons (k', v, tl) ->
      match T.equal k' k with
      | None -> find k tl
      | Some eq -> Some (cast eq v)

end

