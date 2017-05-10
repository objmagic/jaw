(* Leftist Heap with invariants enforced by GADT *)
open Nat

module type OrderedType = sig
  type t
  val compare: t -> t -> int
end

module type HEAP = sig
  type elt
  type t

  val empty : t
  val merge : t -> t -> t
  val insert : elt -> t -> t
  val find_min : t -> elt option
  val delete_min : t -> t option
end

module LeftistHeap (O : OrderedType) : HEAP with type elt = O.t = struct
  type elt = O.t

  (* shape enforced leftist tree *)
  type _ tree =
    | Empty : z tree
    (* the rank of left child is at least as large as the rank of right sibling *)
    | Node : ('r s) nat * ('r, 'l) le * 'l tree * elt * 'r tree -> ('r s) tree
  type t = Exists : 'r tree -> t

  let rank : type r. r tree -> r nat = function
    | Empty -> Z
    | Node (r, _, _, _, _) -> r

  (* swap if the rank of right one is larger than left one *)
  let make_node (Exists a) x (Exists b) =
    let n = rank a in
    let m = rank b in
    match le_total n m with
    | Ok hle -> Exists (Node (S n, hle, b, x, a))
    | Error hle -> Exists (Node (S m, hle, a, x, b))

  let empty = Exists Empty

  let rec merge h1 h2 =
    match h1, h2 with
    | Exists Empty, _ -> h2
    | _, Exists Empty -> h1
    | Exists (Node (_, _, a1, x, b1)), Exists (Node (_, _, a2, y, b2)) ->
        if O.compare x y <= 0 then make_node (Exists a1) x (merge (Exists b1) h2)
        else make_node (Exists a2) y (merge h1 (Exists b2))

  let insert x = merge (Exists (Node (S Z, LeEq, Empty, x, Empty)))

  let find_min = function
    | Exists Empty -> None
    | Exists (Node (_, _, _, x, _)) -> Some x

  let delete_min = function
    | Exists Empty -> None
    | Exists (Node (_, _, l, _, r)) -> Some (merge (Exists l) (Exists r))
end

(* test codes *)
module Int = struct
  type t = int
  let compare = compare
end

module IntLeftistHeap = LeftistHeap (Int)

let heap = List.fold_right IntLeftistHeap.insert [1; 1; 4; 5; 1; 4; 8; 10] IntLeftistHeap.empty
let rec dump heap =
  match IntLeftistHeap.find_min heap with
  | None -> ()
  | Some e ->
      Printf.printf "%d\n" e;
      begin match IntLeftistHeap.delete_min heap with
      | None -> ()
      | Some heap' -> dump heap'
      end

let () = dump heap
