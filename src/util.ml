open Core

open Lexing

let string_of_pos pos =
  sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  (* pos.pos_cnum *)

let import_error msg pos = eprintf "Import error at %s: %s\n" (string_of_pos pos) msg; exit (-1)

let type_error msg pos = eprintf "Type error at %s: %s\n" (string_of_pos pos) msg; exit (-1)

let label_error msg pos = eprintf "Label error at %s: %s\n" (string_of_pos pos) msg; exit (-1)

let take l n =
  let rec aux = function
    | _, 0 -> []
    | [], _ -> raise (Invalid_argument (string_of_int n))
    | x::xs, i -> x :: aux (xs, (i - 1))
  in
  aux (l, n)
