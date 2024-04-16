open Core

open Lexing

let string_of_pos pos =
  sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  (* pos.pos_cnum *)

let type_error msg pos = eprintf "Type error at %s: %s\n" (string_of_pos pos) msg; exit (-1)

let rec take l n =
  match l, n with
  | _, 0 -> []
  | [], _ -> []
  | x::xs, n -> x :: take xs (n - 1)