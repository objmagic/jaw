(* Two implementations of heterogeneous maps,
   from discussions between Jeremy and me *)

module type HMAP = sig
  type _ key
  type _ value
  type t
  val fresh_key : unit -> 'a key
  val empty : t
  val add : t -> 'a key -> 'a value -> t
  val find : t -> 'a key -> 'a value option
end

module Modern : HMAP = struct

  type _ k' = ..

  type (_, _) eql = Refl : ('a, 'a) eql

  type 'a key = {
    k : 'a k';
    eq : 'b. 'b k' -> ('a, 'b) eql option
  }

  type _ value

  let fresh_key (type a) () =
    let module M = struct type _ k' += T : a k' end in
    let eq : type b. b k' -> (a, b) eql option =
      function M.T -> Some Refl | _ -> None in
    {k = M.T; eq}

  type t = Nil | Cons : 'a key * 'a value * t -> t

  let empty = Nil

  let add t k v = Cons (k, v, t)

  let rec find : type a. t -> a key -> a value option =
    fun t k ->
      match t with
      | Nil -> None
      | Cons ({k = k'}, v, rest) ->
        match k.eq k' with
        | Some Refl -> Some v
        | None -> find rest k

end

(* No GADT or first-class module free involved, but is much
   more tricky. You may need to ponder for a while to understand
   its mechanism *)
module OldSchool : HMAP = struct

  type s = bool -> unit

  type 'a key = ('a value -> s) * (s -> 'a value option)
  and _ value

  (* Consider [inj] as a pair buttons. Pressing "true" button puts value inside
     box, and pressing "false" button takes the item in box outside *)
  let fresh_key () =
    let r = ref None in
    let inj x b = r := if b then Some x else None in
    let prj f = f true; let res = !r in f false; res in
    (inj, prj)

  type t = s list

  let empty = []

  let add l (inj, _) v = inj v :: l

  let rec find t ((inj, prj) as k) = match t with
      [] -> None
    | x :: xs ->
      match prj x with
        Some v -> Some v
      | None -> find xs k
end
