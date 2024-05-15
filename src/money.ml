open Core

type t = Money of int * string

let ($) a c = Money (int_of_float (a *. 100.), c)

let same_currency m m' = String.equal m m'

let currency (Money (_, c)) = c
let amount (Money (a, _)) = float_of_int a /. 100.
let units (Money (a, _)) = a / 100
let cents (Money (a, _)) = a mod 100

let (+) (Money (a, m)) (Money (a', m')) =
  assert (same_currency m m');
  Money (a + a', m)

let (-) (Money (a, m)) (Money (a', m')) =
  assert (same_currency m m');
  Money (a - a', m)

let ( * ) s (Money (a, m)) =
  Money (s * a, m)

let to_string m =
  Printf.sprintf "%s %d.%02d" (currency m) (units m) (cents m)
