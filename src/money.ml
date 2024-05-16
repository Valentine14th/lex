open Core

type t = M of int * string

let ($) a c = M (int_of_float (a *. 100.), c)

let same_currency m m' = String.equal m m'

let currency (M (_, c)) = c
let amount (M (a, _)) = float_of_int a /. 100.
let units (M (a, _)) = a / 100
let cents (M (a, _)) = a mod 100

let (+) (M (a, m)) (M (a', m')) =
  assert (same_currency m m');
  M (a + a', m)

let (-) (M (a, m)) (M (a', m')) =
  assert (same_currency m m');
  M (a - a', m)

let ( * ) s (M (a, m)) =
  M (s * a, m)

let to_string m =
  Printf.sprintf "%s %d.%02d" (currency m) (units m) (cents m)
