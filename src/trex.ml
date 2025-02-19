open Core
open Lex
open Rex
open Tlex

(* Statements and programs *)

type trrule =
  | TRefine   of LexingInfo.t * Pattern.t * Tformula.t list

type trtmt =
  | TRStmt    of tstmt
  | TRRule    of LexingInfo.t * int * Label.t * (ident * TypeTerm.t) list * trrule * string tannot option
  | TRType    of LexingInfo.t * ident * TypeTerm.t option * string option
  | TRReplace of LexingInfo.t * replace_kind * Ref.t list * Ref.t list * string option
  | TRHide    of LexingInfo.t * ident * string option

type trefi =
  {
    tprog:          tprog;
    trtmts:         trtmt list;
    theory:         string list;
    traliases:      (ident, TypeTerm.t option * string option, Base.String.comparator_witness) Map.t;
    trhidden:       (LexingInfo.t * ident) list;
    trrefined:      (ident, Base.String.comparator_witness) Set.t;
    trreplacements: (LexingInfo.t * replace_kind * Ref.t list * Ref.t list) list;
  }

let trempty =
  {
    tprog          = tempty;
    trtmts         = [];
    theory         = [];
    traliases      = Map.empty (module String);
    trhidden       = [];
    trrefined      = Set.empty (module String);
    trreplacements = [];
  }


(* Printing functions *)

let string_of_trrule i rule =
  let open Pattern in
  let to_string (f: Tformula.t) = Util.tabs (i+1) ^ Tformula.to_string f in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:(fun f -> to_string f) f) ^ "\n" in
  let string_of_refine_rule fp g =
    Util.tabs i     ^ "whenever" ^ patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Util.tabs i   ^ "refine"   ^ "\n"
    ^ string_of_formula_list g
  in
  match rule with
  | TRefine (_, fp, g)
    -> string_of_refine_rule fp g

let string_of_trtmt ?(i=0) =
  let string_of_ref r = Util.tabs (i+1) ^ Ref.to_string r in
  function
  | TRStmt tstmt ->
     string_of_tstmt ~i tstmt
  | TRRule (_, _, label, type_fixes, trrule, doc_string) ->
     let description = 
       match doc_string with
       | Some s -> "\n" ^ make_doc_string (of_annot s) i
       | None -> ""
      in
     Printf.sprintf "%srule%s\n%s%s\n%s"
       (Util.tabs i)
       (Label.qualified_name label)
       (string_of_type_fixes (i+1) type_fixes)
       (string_of_trrule (i+1) trrule)
       description
  | TRType (_, name, typ, doc_string) ->
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
  | TRReplace (_, kind, refs1, refs2, doc_string) ->
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
  | TRHide (_, name, doc_string) ->
      let description =
        match doc_string with
        | Some s -> make_doc_string s i
        | None -> ""
      in
      Printf.sprintf "%shide %s%s" (Util.tabs i) name description

let string_of_trefi refi =
  "refine " ^ String.concat ~sep:"." refi.theory ^ "\n" 
  ^ String.concat ~sep:"\n" (List.map refi.trtmts ~f:string_of_trtmt)
      
let print_trefi refi =
  Stdio.printf "%s\n" (string_of_trefi refi)
