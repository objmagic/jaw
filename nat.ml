(* Arithmetics *)

type z = unit
type 'n s = 'n option

type _ nat =
  | Z : z nat
  | S : 'n nat -> 'n s nat

(* "('n, 'm) le" means n <= m *)
type (_, _) le =
  | LeEq : ('n, 'n) le
  | LeS : ('n, 'm) le -> ('n, 'm s) le

let le_refl = LeEq

let rec le_trans : type l m n. (l, m) le -> (m, n) le -> (l, n) le = fun hle1 -> function
  | LeEq -> hle1
  | LeS hle2 -> LeS (le_trans hle1 hle2)

let rec le_n_s : type n m. (n, m) le -> (n s, m s) le = function
  | LeEq -> LeEq
  | LeS hle -> LeS (le_n_s hle)

let rec le_0_n : type n. n nat -> (z, n) le = function
  | Z -> LeEq
  | S n -> LeS (le_0_n n)

let rec le_total : type n m. n nat -> m nat -> ((n, m) le, (m, n) le) result = fun n m ->
    match n, m with
    | Z, _ -> Ok (le_0_n m)
    | _, Z -> Error (le_0_n n)
    | S n', S m' ->
        begin match le_total n' m' with
        | Ok hle -> Ok (le_n_s hle)
        | Error hge -> Error (le_n_s hge)
        end

