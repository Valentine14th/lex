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
  | TRAssume  of LexingInfo.t * ident * bool * string option

type trefi =
  {
    tprog:          tprog;
    trtmts:         trtmt list;
    lex_file:       string list;
    traliases:      (ident, TypeTerm.t option * string option, Base.String.comparator_witness) Map.t;
    trassumed:      (LexingInfo.t * ident * bool * Label.t) list;
    trvars_to_add:  (int * var_types) list;
    trrules_to_add: (LexingInfo.t * int * Label.t) list;
    trstmts_to_add: tstmt list;
    trrefined:      (ident, Base.String.comparator_witness) Set.t;
    trreplacements: (LexingInfo.t * replace_kind * Ref.t list * Ref.t list) list;
    tr_mon:         (ident, LexingInfo.t, Base.String.comparator_witness) Map.t;
    tr_anti_mon:    (ident, LexingInfo.t, Base.String.comparator_witness) Map.t;
  }

let trempty =
  {
    tprog          = tempty;
    trtmts         = [];
    lex_file       = [];
    traliases      = Map.empty (module String);
    trassumed      = [];
    trvars_to_add  = [];
    trrules_to_add = [];
    trstmts_to_add = [];
    trrefined      = Set.empty (module String);
    trreplacements = [];
    tr_mon         = Map.empty (module String);
    tr_anti_mon    = Map.empty (module String);
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
  | TRAssume (_, name, b, doc_string) ->
      let description =
        match doc_string with
        | Some s -> make_doc_string s i
        | None -> ""
      in
      Printf.sprintf "%shide %b %s%s" (Util.tabs i) b name description

let string_of_trefi refi =
  "refine " ^ String.concat ~sep:"." refi.lex_file ^ "\n" 
  ^ String.concat ~sep:"\n" (List.map refi.trtmts ~f:string_of_trtmt)
      
let print_trefi refi =
  Stdio.printf "%s\n" (string_of_trefi refi)
