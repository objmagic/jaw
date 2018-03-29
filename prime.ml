(* prove a number is prime using GADT.
   needs to use OCaml 4.03.0 which has refutation case support

   written by Jeremy Yallop *)

type z = Z
type _ s = S

type (_, _, _) add =
  | Zz: (z, z, z) add
  | Zr: ('a, 'b, 'c) add -> ('a, 'b s, 'c s) add

type (_, _, _) mul =
  | Mone : (z s, 'a, 'a) mul
  | Mn : ('m, 'o, 'n) mul * ('n, 'o, 'p) add -> ('m s, 'o, 'p) mul

type absurd = {p: 'a. 'a}

type 'a neg = 'a -> absurd

(* a number n is composite if there exists two numbers >= 2 and their production is n *)
type 'a composite =
  C : (_ s s, _ s s, 'a) mul -> 'a composite

type 'a prime = 'a composite neg

type two = z s s

let two_is_prime : two prime = function
  | C (Mn (Mone, Zr Zr _)) -> .
  | C (Mn (Mn _, Zr Zr _)) -> .
