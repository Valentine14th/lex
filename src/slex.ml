open Core

(* Temporal patterns *)

module SPattern = Pattern.MakeSimple(Sformula)

open Lex

(* Rule declarations *)

type srule =
  | SObligation   of LexingInfo.t * SPattern.t * SPattern.t * rule_type * rule_constr list
  | SPermission   of LexingInfo.t * SPattern.t * SPattern.t * rule_type * rule_constr list
  | SConstitutive of LexingInfo.t * SPattern.t * Sformula.t list
  | SException    of LexingInfo.t * SPattern.t * Ref.t list
  | SExceptionC   of LexingInfo.t * SPattern.t * Ref.t list * Sformula.t list
  | SScope        of LexingInfo.t * SPattern.t * Ref.t list

let pos_of_srule = function
  | SObligation   (pos, _, _, _, _) -> pos
  | SPermission   (pos, _, _, _, _) -> pos
  | SConstitutive (pos, _, _)       -> pos
  | SException    (pos, _, _)       -> pos
  | SExceptionC   (pos, _, _, _)    -> pos
  | SScope        (pos, _, _)       -> pos

(* Statements and programs *)

type sstmt =
  | SSImport    of LexingInfo.t * import_format * string list
  | SSInclude   of LexingInfo.t * string list
  | SSSection   of LexingInfo.t * section_kind * string * string option
  | SSRule      of LexingInfo.t * string option * (ident * TypeTerm.t) list * srule * string option
  | SSEvent     of LexingInfo.t * event_type * ident * (ident * TypeTerm.t) list * Enftype.t * string option
  | SSType      of LexingInfo.t * ident * (TypeTerm.t option) * string option
  | SSFunction  of LexingInfo.t * ident * (ident * TypeTerm.t) list * TypeTerm.t * string option
  | SSNote      of LexingInfo.t * string

type sprog = { stmts: sstmt list }

(* Conversion to lex *)

let rec to_core_pattern = function
  | SPattern.PPresent -> Pattern.PPresent
  | PEventually i -> PEventually i
  | PAlways i -> PAlways i
  | PUntil (i, f) -> PUntil (i, Formula.init f)
  | POnce i -> POnce i
  | PHistorically i -> PHistorically i
  | PSince (i, f) -> PSince (i, Formula.init f)
and to_pattern (p: SPattern.t) =
  Pattern.make (to_core_pattern p.patt) (List.map ~f:Formula.init p.fs)

let to_rule = function
  | SObligation (pos, fp1, fp2, rt, rcs) -> Obligation (pos, to_pattern fp1, to_pattern fp2, rt, rcs)
  | SPermission (pos, fp1, fp2, rt, rcs) -> Permission (pos, to_pattern fp1, to_pattern fp2, rt, rcs)
  | SConstitutive (pos, fp, g) -> Constitutive (pos, to_pattern fp, List.map ~f:Formula.init g)
  | SException (pos, fp, references) -> Exception (pos, to_pattern fp, references)
  | SScope (pos, fp, references) -> Scope (pos, to_pattern fp, references)
  | SExceptionC (pos, fp, references, g) -> ExceptionC (pos, to_pattern fp, references, List.map ~f:Formula.init g)

let replace_includes (incl_map: (string, sprog, String.comparator_witness) Map.t) sprog =
  let replace_include_stmt = function
    | SSInclude (_, idents) -> (Map.find_exn incl_map (Util.concat_all_filename idents)).stmts
    | stmt -> [stmt]
  in
  { stmts = List.concat_map ~f:replace_include_stmt sprog.stmts }
    
let to_stmt = function
  | SSImport (pos, import_format, idents) -> SImport (pos, import_format, idents)
  | SSInclude _ -> assert false
  | SSSection (pos, section_kind, label, title) -> SSection (pos, section_kind, label, title)
  | SSRule (pos, label, type_fixes, rule, doc_string) -> SRule (pos, label, type_fixes, to_rule rule, doc_string)
  | SSEvent (pos, event_type, name, typed_args, pol, doc_string) -> SEvent (pos, event_type, name, typed_args, pol, doc_string)
  | SSType (pos, name, typ, doc_string) -> SType (pos, name, typ, doc_string)
  | SSFunction (pos, name, typed_args, return_typ, doc_string) -> SFunction (pos, name, typed_args, return_typ, doc_string)
  | SSNote (pos, text) -> SNote (pos, text)

let to_prog (sprog: sprog) = Lex.{ stmts = List.map ~f:to_stmt sprog.stmts }

(* Printing functions *)
    
let verb_of_rule = function
  | SObligation _ -> "oblige"
  | SPermission _ -> "permit"
  | SConstitutive _ -> "constitute"
  | SException _ 
    | SExceptionC _ -> "except"
  | SScope _ -> "scope"

let string_of_rule i rule =
  let open SPattern in
  let to_string (f: Sformula.t) = Util.tabs (i+1) ^ Sformula.to_string f in
  let string_of_formula_list (fs: Sformula.t list) =
    String.concat ~sep:"\n" (List.map ~f:(fun f -> to_string f) fs) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Util.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_imp_rule verb (fp1: t) (fp2: t) rcs rt =
    Util.tabs i     ^ "whenever" ^ patt_to_string fp1.patt ^ "\n"
    ^ string_of_formula_list fp1.fs ^ "\n"
    ^ Util.tabs i   ^ verb       ^ patt_to_string fp2.patt ^ "\n"
    ^ string_of_formula_list fp2.fs
    ^ Util.tabs i ^ string_of_rule_type rt (* TODO: check that this prints the rule_type correctly *)
    ^ (if List.is_empty rcs then "" (* TODO: check that this prints the rule_constr list correctly *)
      else Util.tabs i ^ (string_of_rule_constrs rcs))
  in
  let string_of_cons_rule verb fp g =
    Util.tabs i     ^ "whenever" ^ patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Util.tabs i   ^ verb      ^ "\n"
    ^ string_of_formula_list g
  in
  let string_of_exc_rule verb fp rs = Util.tabs i     ^ "whenever"  ^ patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Util.tabs i   ^ verb
    ^ String.concat ~sep:"\n" (List.map ~f:Ref.to_string rs)
  in
  let string_of_excc_rule verb fp rs g =
    Util.tabs i     ^ "whenever"  ^ patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Util.tabs i   ^ verb
    ^ String.concat ~sep:"\n" (List.map ~f:Ref.to_string rs)
    ^ Util.tabs i   ^ "constitute"
    ^ string_of_formula_list g
  in
  match rule with
  | SObligation (_, fp1, fp2, rt, rcs)
  | SPermission (_, fp1, fp2, rt, rcs)
    -> string_of_imp_rule (verb_of_rule rule) fp1 fp2 rcs rt
  | SConstitutive (_, fp, g)
    -> string_of_cons_rule (verb_of_rule rule) fp g
  | SException (_, fp, references)
  | SScope (_, fp, references)
    -> string_of_exc_rule (verb_of_rule rule) fp references
  | SExceptionC (_, fp, references, g)
    -> string_of_excc_rule (verb_of_rule rule) fp references g

let string_of_stmt ?(i=0) =
  function
  | SSImport (_, import_format, idents) ->
     Printf.sprintf "import %s%s"
       (string_of_import_format import_format)
       (String.concat ~sep:"." idents)
  | SSInclude (_, idents) ->
     Printf.sprintf "include %s"
       (String.concat ~sep:"." idents)
  | SSSection (_, section_kind, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Util.tabs i)
       (string_of_section_kind section_kind)
       label
       (match title with Some title -> Printf.sprintf " \"%s\"" title | None -> "")
  | SSRule (_, label, type_fixes, rule, doc_string) ->
     let description = 
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> ""
      in
     Printf.sprintf "%srule%s\n%s%s\n%s"
       (Util.tabs i)
       (Option.value_map label ~default:"" ~f:(fun label -> " " ^ label))
       (string_of_type_fixes (i+1) type_fixes)
       (string_of_rule (i+1) rule)
       description
  | SSEvent (_, event_type, name, typed_args, pol, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
      Printf.sprintf "%s%s %s %s\n%s%s"
          (Util.tabs i)
          (string_of_enftype pol)
          (string_of_event_type event_type)
          name
          description
          (string_of_args typed_args i)
  | SSType (_, name, typ, doc_string) ->
     let description =
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> "" in
     let typ_string =
       match typ with
       | Some tt -> " is " ^ TypeTerm.to_string tt
       | None -> "" in
     Printf.sprintf "%stype %s%s%s"
       (Util.tabs i) name typ_string description
  | SSFunction (_, name, typed_args, return_typ, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string s i
          | None -> ""
     in
     let f (ident, typ) = Printf.sprintf "%s : %s" ident (TypeTerm.value_to_string typ) in
     Printf.sprintf "%sfunction %s(%s) -> %s%s"
       (Util.tabs i)
       name
       (String.concat ~sep:", " (List.map typed_args ~f))
       (TypeTerm.to_string return_typ)
       description
  | SSNote (_, text) -> "note \"" ^ text ^ "\""

let string_of_prog prog =
  String.concat ~sep:"\n" (List.map prog.stmts ~f:string_of_stmt)
      
let print_prog prog =
  Stdio.printf "%s\n" (string_of_prog prog)


