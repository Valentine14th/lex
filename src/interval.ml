(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Lextime
open Core

type bound = C of Span.t | O of Span.t 

let equal_bound b b' = match b, b' with
  | C s, C s' -> Span.equal s s'
  | O s, O s' -> Span.equal s s'
  | _         -> false

let leq_bounds b b' = match b, b' with
  | C s, C s' -> Span.(s <= s')
  | O s, O s' -> Span.(s <= s')
  | C s, O s' -> Span.(s < s')
  | O s, C s' -> Span.(s < s')

let lt_bounds b b' = match b, b' with
  | C s, C s' -> Span.(s < s')
  | O s, O s' -> Span.(s < s')
  | C s, O s' -> Span.(s < s')
  | O s, C s' -> Span.(s < s')

let compare_bound b b' = match b, b' with
  | C s, C s' -> Span.compare s s'
  | O s, O s' -> Span.compare s s'
  | C _, O _  -> 1
  | O _, C _ -> -1

let sexp_of_bound = function
  | C s -> Sexp.List [Sexp.Atom "C"; Span.sexp_of_t s]
  | O s -> Sexp.List [Sexp.Atom "O"; Span.sexp_of_t s]

let hash_fold_bound state = function
  | C s -> hash_fold_list hash_fold_int state [0; Span.hash s]
  | O s -> hash_fold_list hash_fold_int state [1; Span.hash s]

type t = B of bound * bound | U of bound [@@deriving compare, sexp_of, hash]

let equal i i' = match i, i' with
  | B (lb, ub), B (lb', ub') -> equal_bound lb lb' && equal_bound ub ub'
  | U lb,       U lb'        -> equal_bound lb lb'
  | _                        -> false

let lclosed_UI s = U (C s)
let lopen_UI s   = U (O s)

let nonempty_BI lb rb =
  if lt_bounds lb rb then
    true
  else
    raise (Invalid_argument "empty interval")

let lopen_ropen_BI ls rs = B (O ls, O rs)
let lopen_rclosed_BI ls rs = B (O ls, C rs)
let lclosed_ropen_BI ls rs = B (C ls, O rs)
let lzero_ropen_BI s = B (C Span.zero, O s)
let lclosed_rclosed_BI ls rs = B (C ls, C rs)
let lzero_rclosed_BI s = B (C Span.zero, C s)

let singleton s = lclosed_rclosed_BI s s
let is_zero s = Span.equal s Span.zero

let has_zero = function
  | B (C s, _) 
    | U (C s) when Span.equal s Span.zero -> true
  | _ -> false

let full = U (C Span.zero)

let case f1 f2 = function
  | B (i, j) -> f1 (i, j)
  | U i -> f2 i

let is_bounded = function
  | B _ -> true
  | U _ -> false

let is_bounded_exn op = function
  | B _ -> ()
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator: %s" op))

let map f1 f2 = case (fun (i, j) -> let i', j' = f1 (i, j) in B (i', j')) (fun i -> U (f2 i))

let to_string = function
  | U (C s) when Span.equal s Span.zero -> ""
  | U (C s) -> Printf.sprintf "[%s,∞)" (Span.to_string s)
  | U (O s) -> Printf.sprintf "(%s,∞)" (Span.to_string s)
  | B (C ls, C rs) -> Printf.sprintf "[%s,%s]" (Span.to_string ls) (Span.to_string rs)
  | B (C ls, O rs) -> Printf.sprintf "[%s,%s)" (Span.to_string ls) (Span.to_string rs)
  | B (O ls, C rs) -> Printf.sprintf "(%s,%s]" (Span.to_string ls) (Span.to_string rs)
  | B (O ls, O rs) -> Printf.sprintf "(%s,%s)" (Span.to_string ls) (Span.to_string rs)
