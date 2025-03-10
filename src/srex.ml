open Core

open Lex
open Rex
open Slex

(* Statements and refinements *)

type srrule =
  | SRefine of LexingInfo.t * SPattern.t * Sformula.t list

let pos_of_srrule = function
  | SRefine (pos, _, _) -> pos

type srtmt =
  | SRStmt     of sstmt
  | SRRefine   of LexingInfo.t * string list
  | SRRule     of LexingInfo.t * string option * (ident * TypeTerm.t) list * srrule * string option
  | SRType     of LexingInfo.t * ident * (TypeTerm.t option) * string option
  | SRReplace  of LexingInfo.t * replace_kind * Ref.t list * Ref.t list * string option
  | SRAssume   of LexingInfo.t * string * bool * string option

type srefi = { rtmts: srtmt list }

(* Conversion to rex *)

let to_rrule : srrule -> rrule = function
  | SRefine (pos, fp, g) -> Refine (pos, to_pattern fp, List.map ~f:Formula.init g)

let replace_includes (incl_map: (string, srefi, String.comparator_witness) Map.t) (srefi: srefi) : srefi =
  let replace_include_rtmt = function
    | SRStmt (SSInclude (_, idents)) -> (Map.find_exn incl_map (Util.concat_all_filename idents)).rtmts
    | rtmt -> [rtmt]
  in
  { rtmts = List.concat_map ~f:replace_include_rtmt srefi.rtmts }
    
let to_rtmt : srtmt -> rtmt = function
  | SRStmt sstmt -> RStmt (to_stmt sstmt)
  | SRRule (pos, label, type_fixes, rrule, doc_string) -> RRule (pos, label, type_fixes, to_rrule rrule, doc_string)
  | SRType (pos, name, typ, doc_string) -> RType (pos, name, typ, doc_string)
  | SRReplace (pos, kind, refs1, refs2, doc_string) -> RReplace (pos, kind, refs1, refs2, doc_string)
  | SRAssume (pos, name, b, doc_string) -> RAssume (pos, name, b, doc_string)
  | SRRefine _ -> assert false

let to_refi (srefi: srefi) : refi =
  match srefi.rtmts with
  | SRRefine (_, lex_file) :: rtmts -> { rtmts = List.map ~f:to_rtmt rtmts; lex_file }
  | _ -> assert false

(* Printing functions *)

let string_of_rrule i rrule =
  let open SPattern in
  let to_string (f: Sformula.t) = Util.tabs (i+1) ^ Sformula.to_string f in
  let string_of_formula_list (fs: Sformula.t list) =
    String.concat ~sep:"\n" (List.map ~f:(fun f -> to_string f) fs) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Util.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_refine_rule fp g =
    Util.tabs i       ^ "whenever" ^ patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs                          ^ "\n"
    ^ Util.tabs i     ^ "refine"                            ^ "\n"
    ^ string_of_formula_list g
  in
  match rrule with
  | SRefine (_, fp, g)
    -> string_of_refine_rule fp g

let string_of_rtmt ?(i=0) =
  let string_of_ref r = Util.tabs (i+1) ^ Ref.to_string r in
  function
  | SRStmt sstmt -> string_of_stmt ~i sstmt
  | SRRefine (_, idents) ->
     Printf.sprintf "%srefine %s" (Util.tabs i) (String.concat ~sep:"." idents)
  | SRRule (_, label, type_fixes, rrule, doc_string) ->
     let description =
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> "" in
     Printf.sprintf "%srule%s\n%s%s\n%s"
       (Util.tabs i)
       (Option.value_map label ~default:"" ~f:(fun label -> " " ^ label))
       (string_of_type_fixes (i+1) type_fixes)
       (string_of_rrule (i+1) rrule)
       description
  | SRType (_, name, typ, doc_string) ->
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
  | SRReplace (_, kind, refs1, refs2, doc_string) ->
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
  | SRAssume (_, name, b, doc_string) ->
      let description =
        match doc_string with
        | Some s -> make_doc_string s i
        | None -> ""
      in
      Printf.sprintf "%shide %b %s%s" (Util.tabs i) b name description

let string_of_prog prog =
  String.concat ~sep:"\n" (List.map prog.stmts ~f:string_of_stmt)
      
let print_prog prog =
  Stdio.printf "%s\n" (string_of_prog prog)


