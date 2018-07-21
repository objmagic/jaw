(* AVL tree with invariants enforced by GADT *)

type compare = LessThan | Equal | GreaterThan

module RawAVLTree = struct

  type z = Z : z and 'n s = S : 'n -> 'n s

  (* Depths of branches of a AVL tree node differs at most by 1 *)
  type (_, _, _) diff =
    | Less : ('a, 'a s, 'a s) diff
    | Same : ('a, 'a, 'a) diff
    | More : ('a s, 'a, 'a s) diff

  (* each tree node has a diff that records left and right trees height
     difference *)
  type ('a, 'd) atree =
    | Empty : ('a, z) atree
    | Tree  : ('a, 'm) atree * 'a * ('a, 'n) atree
              * ('m, 'n, 'o) diff -> ('a, 'o s) atree

  exception Empty_tree

  (* for insertion *)
  type ('a, _) pos_result =
    | PSameDepth : ('a, 'd) atree -> ('a, 'd) pos_result
    | Deeper : ('a, 'd s) atree -> ('a, 'd) pos_result

  (* for deletion *)
  type ('a, _) neg_result =
    | NSameDepth  : ('a, 'd s) atree -> ('a, 'd s) neg_result
    | Shallower : ('a, 'd) atree -> ('a, 'd s) neg_result

  let is_empty : type d. ('a, d) atree -> bool = function
    | Empty -> true
    | _ -> false

  let rec member : type d. ('a -> 'a -> compare) -> 'a -> ('a, d) atree -> bool =
    fun cmp ele t ->
      match t with
      | Empty -> false
      | Tree (l, k, r, _) ->
        match cmp ele k with
        | LessThan -> member cmp ele l
        | Equal -> true
        | GreaterThan -> member cmp ele r

  let rec in_order_iter : type d. ('a -> unit) -> ('a, d) atree -> unit =
    fun iter t ->
      match t with
      | Empty -> ()
      | Tree (l, k, r, _) ->
        in_order_iter iter l;
        iter k;
        in_order_iter iter r

  (* canonical AVL rotation algorithm now in GADT. Implementation
     is guaranteed to be correct thanks to GADT *)
  let rotate_left : type d. ('a, d) atree -> 'a -> ('a, d s s) atree -> ('a, d s s) pos_result =
    fun l v r ->
      let Tree (rl, rv, rr, diff) = r in
      match diff with
      | Less -> PSameDepth (Tree (Tree (l, v, rl, Same), rv, rr, Same))
      | Same -> Deeper (Tree (Tree (l, v, rl, Less), rv, rr, More))
      | More -> begin
        let Tree (rll, rlv, rlr, diffl) = rl in
        match diffl with
        | Less -> PSameDepth (Tree (Tree (l, v, rll, More), rlv, Tree (rlr, rv, rr, Same), Same))
        | Same -> PSameDepth (Tree (Tree (l, v, rll, Same), rlv, Tree (rlr, rv, rr, Same), Same))
        | More -> PSameDepth (Tree (Tree (l, v, rll, Same), rlv, Tree (rlr, rv, rr, Less), Same))
        end

  let rotate_right : type d. ('a, d s s) atree -> 'a -> ('a, d) atree -> ('a, d s s) pos_result =
    fun l v r ->
      let Tree (ll, lv, lr, diff) = l in
      match diff with
      | More -> PSameDepth (Tree (ll, lv, (Tree (lr, v, r, Same)), Same))
      | Same -> Deeper (Tree (ll, lv, (Tree (lr, v, r, More)), Less))
      | Less -> begin
          let Tree (lrl, lrv, lrr, diffr) = lr in
          match diffr with
          | Less -> PSameDepth (Tree (Tree (ll, lv, lrl, More), lrv, Tree (lrr, v, r, Same), Same))
          | Same -> PSameDepth (Tree (Tree (ll, lv, lrl, Same), lrv, Tree (lrr, v, r, Same), Same))
          | More -> PSameDepth (Tree (Tree (ll, lv, lrl, Same), lrv, Tree (lrr, v, r, Less), Same))
        end

  let rec insert : type d. ('a -> 'a -> compare) -> 'a -> ('a, d) atree -> ('a, d) pos_result =
    fun cmp v t ->
      match t with
      | Empty -> Deeper (Tree (Empty, v, Empty, Same))
      | Tree (l, tv, r, diff) ->
        match cmp v tv with
        | LessThan -> begin
          match insert cmp v l with
          | Deeper t' -> begin
            match diff with
            | More -> rotate_right t' tv r
            | Same -> Deeper (Tree (t', tv, r, More))
            | Less -> PSameDepth (Tree (t', tv, r, Same))
            end
          | PSameDepth t' -> PSameDepth (Tree (t', tv, r, diff))
          end
        | Equal -> PSameDepth t
        | GreaterThan -> begin
          match insert cmp v r with
          | Deeper t' -> begin
            match diff with
            | Less -> rotate_left l tv t'
            | Same -> Deeper (Tree (l, tv, t', Less))
            | More -> PSameDepth (Tree (l, tv, t', Same))
            end
          | PSameDepth t' -> PSameDepth (Tree (l, tv, t', diff))
          end

  let rec min_elt : type d. ('a, d) atree -> 'a = function
    | Empty -> raise Empty_tree
    | Tree (Empty, tv, _, _) -> tv
    | Tree (l, _, _, _) -> min_elt l

  let rec remove_min_elt : type d. ('a, d s) atree -> ('a, d s) neg_result = function
    | Tree (Empty, _, r, Less) -> Shallower r
    | Tree (l, tv, r, Less) -> begin
      match l with
      | Empty -> raise Empty_tree
        (* Weird, it seems that I have to manually write out this constructor!
           Try change the constructor below to wildcard and code won't type check *)
      | Tree _ ->
        let result = remove_min_elt l in
        match result with
        | NSameDepth t -> NSameDepth (Tree (t, tv, r, Less))
        | Shallower t ->
          match rotate_left t tv r with
          | PSameDepth t' -> Shallower t'
          | Deeper t' -> NSameDepth t'
      end
    | Tree (l, tv, r, More) -> begin
      (* It is guranteed that ``l`` cannot be Empty because we already
         specified ``More`` in constructor.
         We only need to do one pattern matching below and compiler
         is smart enough to tell pattern matching is exhaustive *)
      match l with
      | Tree _ as l ->
        let result = remove_min_elt l in
        match result with
        | NSameDepth t -> NSameDepth (Tree (t, tv, r, More))
        | Shallower t -> Shallower (Tree (t, tv, r, Same))
      end
    | Tree (l, tv, r, Same) -> begin
        match l with
        | Empty -> raise Empty_tree
        | Tree _ as l ->
          let result = remove_min_elt l in
          match result with
          | NSameDepth t -> NSameDepth (Tree (t, tv, r, Same))
          | Shallower t -> NSameDepth (Tree (t, tv, r, Less))
      end

  let merge : type m n o. ('a, m) atree -> ('a, n) atree -> (m, n, o) diff -> ('a, o) pos_result =
    fun l r diff ->
      match l, r, diff with
      | Empty, Empty, Same -> PSameDepth Empty
      | Empty, _, Less -> PSameDepth r
      | _, Empty, More -> PSameDepth l
      | Tree _, Tree _, Same -> begin
        let e = min_elt r and result = remove_min_elt r in
        match result with
        | NSameDepth t -> Deeper (Tree (l, e, t, Same))
        | Shallower t -> Deeper (Tree (l, e, t, More))
        end
      | Tree _, Tree _, Less -> begin
        let e = min_elt r and result = remove_min_elt r in
        match result with
        | NSameDepth t -> Deeper (Tree (l, e, t, Less))
        | Shallower t ->  PSameDepth (Tree (l, e, t, Same))
        end
      | Tree _, Tree _, More -> begin
        let e = min_elt r and result = remove_min_elt r in
        match result with
        | NSameDepth t -> Deeper (Tree (l, e, t, More))
        | Shallower t -> rotate_right l e t
        end

  let pos_to_neg : type d. ('a, d) pos_result -> ('a, d s) neg_result = function
    | PSameDepth t -> Shallower t
    | Deeper t -> NSameDepth t

  let rec remove : type d. ('a -> 'a -> compare) -> 'a -> ('a, d) atree -> ('a, d) neg_result =
    fun cmp v t ->
      match t with
      | Empty -> raise Empty_tree
      | Tree (l, tv, r, diff) ->
        match cmp v tv with
        (* < *)
        | LessThan -> begin
          match remove cmp v l with
          | Shallower t -> begin
            match diff with
            | Less -> pos_to_neg (rotate_left t tv r)
            | Same -> NSameDepth (Tree (t, tv, r, Less))
            | More -> Shallower (Tree (t, tv, r, Same))
            end
          | NSameDepth t -> NSameDepth (Tree (t, tv, r, diff))
          end
        (* = *)
        | Equal -> begin
          match merge l r diff with
          | PSameDepth t -> Shallower t
          | Deeper t -> NSameDepth t
          end
        (* > *)
        | GreaterThan -> begin
          match remove cmp v r with
          | Shallower t -> begin
              match diff with
              | Less -> Shallower (Tree (l, tv, t, Same))
              | Same -> NSameDepth (Tree (l, tv, t, More))
              | More -> pos_to_neg (rotate_right l tv t)
            end
          | NSameDepth t -> NSameDepth (Tree (l, tv, t, diff))
          end

end

module type Set = sig
  type t
  type elem
  val empty : t
  val is_empty : t -> bool
  val member : elem -> t -> bool
  val insert : elem -> t -> t
  val remove : elem -> t -> t
  val iter : (elem -> unit) -> t -> unit
end

module Set (X : sig type t val compare : t -> t -> compare end)
     : Set with type elem := X.t = struct
  
  type t = T : (X.t, _) RawAVLTree.atree -> t

  type elem = X.t

  let empty = T (RawAVLTree.Empty)

  let is_empty (T t) = RawAVLTree.(is_empty t)

  let member e (T t) = RawAVLTree.(member X.compare e t)

  let insert e (T t) = RawAVLTree.(
      match insert X.compare e t with
      | PSameDepth t -> T t
      | Deeper t -> T t)

  let remove e (T t) = RawAVLTree.(
      match remove X.compare e t with
      | NSameDepth t -> T t
      | Shallower t -> T t)

  let iter f (T t) = RawAVLTree.(in_order_iter f t)

end

module IntCompare = struct
  type t = int
  let compare i j =
    match () with
    | _ when i < j -> LessThan
    | _ when i = j -> Equal
    | _ -> GreaterThan
end

module IntSet = Set(IntCompare)

let () =
  let open IntSet in
  let add_list l s = List.fold_left (fun acc e -> insert e acc) s l in
  let remove_list l s = List.fold_left (fun acc e -> remove e acc) s l in
  let l1 = [1; 2; 3; 4; 5] and l2 = [1; 2; 3] in
  let s1 = add_list l1 empty in
  assert (member 1 s1);
  assert (member 2 s1);
  assert (member 3 s1);
  assert (member 4 s1);
  assert (member 5 s1);
  let s2 = remove_list l2 s1 in
  assert (not (member 1 s2));
  assert (not (member 2 s2));
  assert (not (member 3 s2));
  assert (member 4 s2);
  assert (member 5 s2);

