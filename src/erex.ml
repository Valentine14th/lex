open Core
open Lex
open Rex
open Tlex
open Elex

(* Statements and programs *)

type errule =
  | ERefine   of LexingInfo.t * Pattern.t * Eformula.t list
  
type ertmt =
  | ERStmt    of estmt
  | ERRule    of LexingInfo.t * int * Label.t * (ident * TypeTerm.t) list * errule * string tannot option
  | ERType    of LexingInfo.t * ident * TypeTerm.t option * string option
  | ERReplace of LexingInfo.t * replace_kind * Ref.t list * Ref.t list * string option
  | ERAssume  of LexingInfo.t * ident * bool * string option

type erefi =
  {
    eprog:          eprog;
    ertmts:         ertmt list;
    lex_file:       string list;
    base_file_type: rfnmt_ext option;
  }

let erempty =
  {
    eprog    = eempty;
    ertmts   = [];
    lex_file = [];
    base_file_type = None;
  }

(* Deconstructors for rules *)

let string_of_errule i rule =
  let open Pattern in
  let to_string (f: Eformula.t) = Util.tabs (i+1) ^ Eformula.to_string f in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:(fun f -> to_string f) f) ^ "\n" in
  let string_of_refine_rule fp g =
    Util.tabs i     ^ "whenever" ^ patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Util.tabs i   ^ "refine"   ^ "\n"
    ^ string_of_formula_list g
  in
  match rule with
  | ERefine (_, fp, g)
    -> string_of_refine_rule fp g

let string_of_ertmt eprog ?(i=0) =
  let string_of_ref r = Util.tabs (i+1) ^ Ref.to_string r in
  function
  | ERStmt estmt ->
     string_of_estmt eprog.ecrules ~i estmt
  | ERRule (_, _, label, type_fixes, errule, doc_string) ->
     let description = 
       match doc_string with
       | Some s -> "\n" ^ make_doc_string (of_annot s) i
       | None -> ""
      in
     Printf.sprintf "%srule%s\n%s%s\n%s"
       (Util.tabs i)
       (Label.qualified_name label)
       (string_of_type_fixes (i+1) type_fixes)
       (string_of_errule (i+1) errule)
       description
  | ERType (_, name, typ, doc_string) ->
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
  | ERReplace (_, kind, refs1, refs2, doc_string) ->
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
  | ERAssume (_, name, b, doc_string) ->
      let description =
        match doc_string with
        | Some s -> make_doc_string s i
        | None -> ""
      in
      Printf.sprintf "%shide %b %s%s" (Util.tabs i) b name description

let string_of_erefi erefi =
  match erefi.base_file_type with
  | Some rfnmt_ext ->
    "refine " ^ string_of_rfnmt_ext rfnmt_ext ^ " " ^ String.concat ~sep:"." erefi.lex_file ^ "\n" 
    ^ String.concat ~sep:"\n" (List.map erefi.ertmts ~f:(string_of_ertmt erefi.eprog))
  | None ->
    "refine " ^ String.concat ~sep:"." erefi.lex_file ^ "\n" 
    ^ String.concat ~sep:"\n" (List.map erefi.ertmts ~f:(string_of_ertmt erefi.eprog))
      
let print_erefi refi =
  Stdio.printf "%s\n" (string_of_erefi refi)
