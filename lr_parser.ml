(* http://gallium.inria.fr/~fpottier/publis/fpottier-regis-gianas-typed-lr.pdf *)
(* Aho 4.1 *)

type token =
  KPlus | KStar | KLeft | KRight | KEnd | KInt of int | EOF

let peek = List.hd and rest = List.tl

module GADT = struct

  type empty = SEmpty
  (* stack *)
  type 'a cP = SP : 'a * 'a state       -> 'a cP (* Plus *)
  and  'a cS = SS : 'a * 'a state       -> 'a cS (* Star *)
  and  'a cL = SL : 'a * 'a state       -> 'a cL (* Left *)
  and  'a cR = SR : 'a * 'a state       -> 'a cR (* Right *)
  (* last field is semantic value *)
  and  'a cI = SI : 'a * 'a state * int -> 'a cI (* Int *)
  and  'a cE = SE : 'a * 'a state * int -> 'a cE (* Expression *)
  and  'a cT = ST : 'a * 'a state * int -> 'a cT (* Term *)
  and  'a cF = SF : 'a * 'a state * int -> 'a cF (* Factor *)

  (* States in action/goto table *)
  and _ state =
    | S0  : empty state
    | S1  : empty cE state
    | S2  : 'a cT state
    | S3  : 'a cF state
    | S4  : 'a cL state
    | S5  : 'a cI state
    | S6  : 'a cE cP state
    | S7  : 'a cT cS state
    | S8  : 'a cL cE state
    | S9  : 'a cE cP cT state
    | S10 : 'a cT cS cF state
    | S11 : 'a cL cE cR state


  let rec action : type a. a state -> token list -> a -> int =
    fun s tl stack ->
      match s, (peek tl) with
      (* S0 *)
      | S0, KInt x -> action S5 (rest tl) (SI (stack, S0, x))
      | S0, KLeft -> action S4 (rest tl) (SL (stack, S0))
      (* S1 *)
      | S1, KPlus -> action S6 (rest tl) (SP (stack, S1))
      | S1, EOF -> let SE (stack, s, v) = stack in v
      (* S2 *)
      | S2, KPlus ->
        let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))
      | S2, KStar ->
        action S7 (rest tl) (SS (stack, s))
      | S2, KRight ->
        let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))
      | S2, EOF ->
        let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))
      (* S3 *)
      | S3, KPlus ->
        let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
      | S3, KStar ->
        let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
      | S3, KRight ->
        let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
      | S3, EOF ->
        let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
      (* S4 *)
      | S4, KInt x -> action S5 (rest tl) (SI (stack, s, x))
      | S4, KLeft -> action S4 (rest tl) (SL (stack, s))
      (* S5 *)
      | S5, KPlus ->
        let SI (stack, s, v) = stack in
        gotoF s tl (SF (stack, s, v))
      | S5, KStar ->
        let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
      | S5, KRight ->
        let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
      | S5, EOF ->
        let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
      (* S6 *)
      | S6, KInt x -> action S5 (rest tl) (SI (stack, s, x))
      | S6, KLeft -> action S4 (rest tl) (SL (stack, s))
      (* S7 *)
      | S7, KInt x -> action S5 (rest tl) (SI (stack, s, x))
      | S7, KLeft -> action S4 (rest tl) (SL (stack, s))
      (* S8 *)
      | S8, KPlus -> action S6 (rest tl) (SP (stack, s))
      | S8, KRight -> action S11 (rest tl) (SR (stack, s))
      (* S9 *)
      | S9, KPlus ->
        let ST (SP (SE (stack, s, x), _), _, y) = stack in
        let stack = SE (stack, s, x + y) in
        gotoE s tl stack
      | S9, KStar -> action S7 (rest tl) (SS (stack, S9))
      | S9, KRight ->
        let ST (SP (SE (stack, s, x), _), _, y) = stack in
        let stack = SE (stack, s, x + y) in
        gotoE s tl stack
      | S9, EOF ->
        let ST (SP (SE (stack, s, x), _), _, y) = stack in
        let stack = SE (stack, s, x + y) in
        gotoE s tl stack
      (* S10 *)
      | S10, KPlus ->
        let SF (SS (ST (stack, s, x), _), _, y) = stack in
        let stack = ST (stack, s, x * y) in
        gotoT s tl stack
      | S10, KStar ->
        let SF (SS (ST (stack, s, x), _), _, y) = stack in
        let stack = ST (stack, s, x * y) in
        gotoT s tl stack
      | S10, KRight ->
        let SF (SS (ST (stack, s, x), _), _, y) = stack in
        let stack = ST (stack, s, x * y) in
        gotoT s tl stack
      | S10, EOF ->
        let SF (SS (ST (stack, s, x), _), _, y) = stack in
        let stack = ST (stack, s, x * y) in
        gotoT s tl stack
      (* S11 *)
      | S11, KPlus ->
        let SR (SE (SL (stack, s), _, v), _) = stack in
        let stack = SF (stack, s, v) in
        gotoF s tl stack
      | S11, KStar ->
        let SR (SE (SL (stack, s), _, v), _) = stack in
        let stack = SF (stack, s, v) in
        gotoF s tl stack
      | S11, KRight ->
        let SR (SE (SL (stack, s), _, v), _) = stack in
        let stack = SF (stack, s, v) in
        gotoF s tl stack
      | S11, EOF ->
        let SR (SE (SL (stack, s), _, v), _) = stack in
        let stack = SF (stack, s, v) in
        gotoF s tl stack
      | _ -> failwith "Invalid grammar"

  (* switch state *)
  and gotoE : type a. a state -> token list -> a cE -> int = fun s tl stack ->
    match s with
    | S0 -> action S1 tl stack
    | S4 -> action S8 tl stack

  and gotoT : type a. a state -> token list -> a cT -> int = fun s tl stack ->
    match s with
    | S0 -> action S2 tl stack
    | S4 -> action S2 tl stack
    | S6 -> action S9 tl stack

  and gotoF : type a. a state -> token list -> a cF -> int = fun s tl stack ->
    match s with
    | S0 -> action S3 tl stack
    | S4 -> action S3 tl stack
    | S6 -> action S3 tl stack
    | S7 -> action S10 tl stack

  let test () = action S0 [KInt 3; KPlus; KInt 2; EOF] SEmpty;;
end
