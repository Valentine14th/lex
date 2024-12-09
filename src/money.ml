open Core

type t = M of int * string [@@deriving compare, sexp_of, hash, equal]

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

let equal (M (a, c)) (M (a', c')) =
  Int.equal a a' && String.equal c c'

let to_string m =
  Printf.sprintf "%s %d.%02d" (currency m) (units m) (cents m)

let sexp_of_t (M (a, c)) = Sexp.List [Int.sexp_of_t a; String.sexp_of_t c]
let hash_fold_t s (M (a, c)) = Hash.fold_string (Hash.fold_int s a) c

let currency_reading = function
  | "USD" -> "$"
  | "EUR" -> "€"
  | "CHF" -> "Fr. "
  | "GBP" -> "£"
  | s -> s ^ " " 
  
let to_string_reading m =
  if cents m > 0 then
    Printf.sprintf "%s%d.%02d" (currency_reading (currency m)) (units m) (cents m)
  else
    Printf.sprintf "%s%d" (currency_reading (currency m)) (units m)
