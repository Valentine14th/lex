open Core
open Lex

(* Statements and programs *)

type replace_kind =
  | Strengthen
  | Weaken

type rrule =
  | Refine    of LexingInfo.t * Pattern.t * Formula.t list

type rtmt =
  | RStmt     of stmt
  | RRule     of LexingInfo.t * string option * (ident * TypeTerm.t) list * rrule * string option
  | RType     of LexingInfo.t * ident * TypeTerm.t option * string option
  | RReplace  of LexingInfo.t * replace_kind * Ref.t list * Ref.t list * string option
  | RAssume   of LexingInfo.t * ident * bool * string option

type rfnmt_ext =
  | RefineLex
  | RefineRex

let string_of_rfnmt_ext = function
  | RefineLex -> "lex"
  | RefineRex -> "rex"

type refi = { rtmts: rtmt list; lex_file: string list; base_file_type: rfnmt_ext option }

(* Printing functions *)

let string_of_rrule i rule =
  let open Pattern in
  let to_string (f: Formula.t) = Util.tabs (i+1) ^ Formula.to_string f in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:(fun f -> to_string f) f) ^ "\n" in
  let string_of_refine_rule fp g =
    Util.tabs i     ^ "whenever" ^ patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Util.tabs i   ^ "refine"   ^ "\n"
    ^ string_of_formula_list g
  in
  match rule with
  | Refine (_, fp, g)
    -> string_of_refine_rule fp g

let string_of_replace_kind = function
  | Strengthen -> "strengthen"
  | Weaken -> "weaken"

let string_of_rtmt ?(i=0) =
  let string_of_ref r = Util.tabs (i+1) ^ Ref.to_string r in
  function
  | RStmt stmt ->
     string_of_stmt ~i stmt
  | RRule (_, label, type_fixes, rule, doc_string) ->
     let description = 
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> ""
      in
     Printf.sprintf "%srule%s\n%s%s\n%s"
       (Util.tabs i)
       (Option.value_map label ~default:"" ~f:(fun label -> " " ^ label))
       (string_of_type_fixes (i+1) type_fixes)
       (string_of_rrule (i+1) rule)
       description
  | RType (_, name, typ, doc_string) ->
     let description =
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> "" in
     let typ_string =
       match typ with
       | Some tt -> " is " ^ TypeTerm.to_string tt
       | None -> "" in
     Printf.sprintf "%srefine type %s%s%s"
       (Util.tabs i) name typ_string description
  | RReplace (_, kind, refs1, refs2, doc_string) ->
     let description =
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> "" in
     Printf.sprintf "%s%s%s%s%s%s\n%sby\n%s%s"
       (Util.tabs i) (string_of_replace_kind kind)
       (Util.tabs (i+1)) description
       (Util.tabs (i+1)) (String.concat ~sep:"\n" (List.map ~f:string_of_ref refs1))
       (Util.tabs i) 
       (Util.tabs (i+1)) (String.concat ~sep:"\n" (List.map ~f:string_of_ref refs2))
  | RAssume (_, name, b, doc_string) ->
      let description =
        match doc_string with
        | Some s -> make_doc_string s i
        | None -> ""
      in
      Printf.sprintf "%shide %b %s%s" (Util.tabs i) b name description

let string_of_refi refi =
  match refi.base_file_type with
  | Some rfnmt_ext ->
    "refine " ^ string_of_rfnmt_ext rfnmt_ext ^ " " ^ String.concat ~sep:"." refi.lex_file ^ "\n" 
    ^ String.concat ~sep:"\n" (List.map refi.rtmts ~f:string_of_rtmt)
  | None ->
    "refine " ^ String.concat ~sep:"." refi.lex_file ^ "\n" 
    ^ String.concat ~sep:"\n" (List.map refi.rtmts ~f:string_of_rtmt)
      
let print_refi refi =
  Stdio.printf "%s\n" (string_of_refi refi)
