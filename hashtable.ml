(** A GADT hash table that allows polymorphic key-value lookup

    Read {{:https://sympa.inria.fr/sympa/arc/caml-list/2013-07/msg00071.html}
     Jeremy Yallop's e-mail reply on Caml-list} for more detail
*)

(** Normal hash table interface *)
module type S = sig
  type key
  type 'a t
  val create : int -> 'a t
  val remove : 'a t -> key -> unit
  val find : 'a t -> key -> 'a
  val iter : (key -> 'a -> unit) -> 'a t -> unit
end

(** GADT hash table interface *)
module type GS = sig
  type 'a key
  (** type of hash table *)
  type t
  type iterator = {f: 'a. 'a key -> 'a -> unit}
  val create : int -> t
  val add : t -> 'a key -> 'a -> unit
  val remove : t -> 'a key -> unit
  (** Polymorphic iter function *)
  val iter : iterator  -> t -> unit
  val find : t -> 'a key -> 'a
end

(** Normal key interface *)
module type HashedType = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
end

(** GADT key interface *)
module type GHashedType = sig
  type _ key
  val equal : _ key -> _ key -> bool
  val hash : _ key -> int

  type pair = Pair : 'a key * 'a -> pair

  (** [unpack k p] retrives value stored in pair [p] using key [k] *)
  val unpack : 'a key -> pair -> 'a
end

module GHashtbl (G : GHashedType) : GS with type 'a key = 'a G.key = struct
  include G

  type k = Key : 'a key -> k

  module H = Hashtbl.Make (struct
      type t = k
      let hash (Key k) = hash k
      let equal (Key k1) (Key k2) = equal k1 k2
    end)

  (** GADT hash table is a regular hash table with value of type [pair] *)
  type t = pair H.t

  let create n = H.create n

  let add tbl k v = H.add tbl (Key k) (Pair (k, v))

  let remove tbl k = H.remove tbl (Key k)

  let find tbl key = unpack key (H.find tbl (Key key))

  type iterator = {f: 'a. 'a key -> 'a -> unit}

  let iter iterator tbl =
    H.iter (fun _ (Pair (k, v)) -> iterator.f k v) tbl

end

module Test = struct

  module KeyType = struct
    type _ key =
      | Int : int -> int list key
      | String : string -> bool key

    let equal : type a b. a key -> b key -> bool = fun k1 k2 ->
      match k1, k2 with
      | Int x, Int y -> x = y
      | String s, String t -> s = t
      | _ -> false

    let hash = Hashtbl.hash

    type pair = Pair : 'a key * 'a -> pair

    let rec unpack : type a. a key -> pair -> a = fun k p ->
      match k, p with
      | Int _, Pair (Int _, v) -> v
      | String _, Pair (String _, v) -> v
      | _ -> raise Not_found
  end

  module HT1 = GHashtbl (KeyType)

  let test1 () =
    let ht = HT1.create 10 in
    HT1.add ht KeyType.(Int 10) [1];
    HT1.add ht KeyType.(String "a") false;
    assert([1] = HT1.find ht KeyType.(Int 10));
    assert(false = HT1.find ht KeyType.(String "a"))

end

