open Core

open Lexing

let string_of_pos pos =
  sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  (* pos.pos_cnum *)

let import_error (msg: string) (pos: Lexing.position) = eprintf "Import error at %s: %s\n" (string_of_pos pos) msg; exit (-1)

let type_error (msg: string) (pos: Lexing.position) = eprintf "Type error at %s: %s\n" (string_of_pos pos) msg; exit (-1)

let label_error (msg: string) (pos: Lexing.position) = eprintf "Label error at %s: %s\n" (string_of_pos pos) msg; exit (-1)

let enf_error (msg: string) (pos: Lexing.position option) = match pos with
  | Some pos -> eprintf "Enforcement error at %s: %s\n" (string_of_pos pos) msg; exit (-1)
  | None -> eprintf "Enforcement error: %s\n" msg; exit (-1)

let reference_error msg pos = eprintf "Reference error at %s: %s\n" (string_of_pos pos) msg; exit(-1)

let compiler_error msg = eprintf "Compiler error: %s\n" msg; exit(-1)

let take l n =
  let rec aux = function
    | _, 0 -> []
    | [], _ -> raise (Invalid_argument (string_of_int n))
    | x::xs, i -> x :: aux (xs, (i - 1))
  in
  aux (l, n)

let butlast l = List.take l (List.length l - 1)

let string_of_string_list l = Printf.sprintf "[%s]"
                              (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s\"%s\";" acc s))

let string_of_string_list_new_line ?(prefix="") l = Printf.sprintf "%s"
                            (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%s%s\n" acc prefix s))
let string_of_int_list l = Printf.sprintf "[%s]"
                           (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%d; " acc s))
let string_of_int_to_int_multi_map m = Printf.sprintf "{%s}"
                                       (List.fold (Int.Map.to_alist m) ~init:"" ~f:(fun acc (k, v) -> Printf.sprintf "%s%d -> %s; " acc k (string_of_int_list v)))

let string_of_int_set s = Printf.sprintf "{%s}"
                           (Set.fold s ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%d; " acc s))

let string_of_string_set s = Printf.sprintf "{%s}"
                           (Set.fold s ~init:"" ~f:(fun acc s -> Printf.sprintf "%s\"%s\"; " acc s))

let string_of_int_set_list l = Printf.sprintf "[%s]"
                               (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%s; " acc (string_of_int_set s)))

let spaces i = String.init i ~f:(fun _ -> ' ')
  
let paren h k x = if h>k then "("^^x^^")" else x
let paren_string h k x = if h>k then "("^x^")" else x

let comb x y =
  match x, y with
  | Some z, _ -> Some z
  | _, Some z -> Some z
  | _, _ -> None

let warning msg pos = match pos with
  | Some p -> eprintf "Warning at %s: %s\n" (string_of_pos p) msg
  | None -> eprintf "Warning: %s\n" msg

let invert_int_string_multimap (m: (int, string list, _) Map.t) : (string, int list, _) Map.t =
  Map.fold m ~init:(Map.empty (module String)) ~f:(fun ~key:k ~data:v acc ->
      List.fold v ~init:acc ~f:(fun acc s ->
          match Map.find acc s with
          | Some l -> Map.set acc ~key:s ~data:(k::l)
          | None -> Map.set acc ~key:s ~data:[k]))

