open Core

module Interval = MFOTL_lib.Interval
module Enftype = MFOTL_lib.Enftype

(* Identifiers *)

type ident = string [@@deriving compare]

(* Imports *)

type import_format =
  | ILex
  | IFormex
  | IAkomaNtoso

(* Section labels *)

type section_kind =
  | Law       of int
  | Title     of int
  | Chapter   of int
  | Section   of int
  | Article   of int
  | Paragraph of int
  | Point     of int
  | Subpoint  of int [@@deriving equal, compare]

let string_of_label_level = function
  | 0 -> ""
  | i -> Printf.sprintf "[%d]" i

let string_of_section_kind = function
  | Law       i -> "law"       ^ string_of_label_level i
  | Title     i -> "title"     ^ string_of_label_level i
  | Chapter   i -> "chapter"   ^ string_of_label_level i
  | Section   i -> "section"   ^ string_of_label_level i
  | Article   i -> "article"   ^ string_of_label_level i
  | Paragraph i -> "paragraph" ^ string_of_label_level i
  | Point     i -> "point"     ^ string_of_label_level i
  | Subpoint  i -> "subpoint"  ^ string_of_label_level i

(* Event declarations *)

type event_syntax =
  | Standard
  | Functional
  | Variable [@@deriving compare, sexp_of, hash, equal]

type event_type =
  | Event of bool * event_syntax
  | Predicate
  | Exception [@@deriving compare, sexp_of, hash, equal]

(* References to a section / rule *)

module Ref = struct

  type t = { sks:  (section_kind * ident) list;
             rule: ident option;
             pos:  LexingInfo.t }

  let make sks rule pos = { sks; rule; pos }

  let to_string (ref: t) =
    let rule_id = match ref.rule with
      | Some r -> " rule \"" ^ r ^ "\""
      | None ->  "" in
    let string_of_section_kind_and_name (s, n) =
      string_of_section_kind s ^ " \"" ^ n ^ "\"" in
    String.concat ~sep:" " (List.map ~f:string_of_section_kind_and_name ref.sks) ^ rule_id 

end

(* Temporal patterns *)

module Pattern = Pattern.Make(Formula.Info)(Formula.StringVar)(Dom)(Term)

(* Rule declarations *)

type rule_type = Vanilla | Enforceable | Transparent [@@deriving equal]

type rule_constr_kind =
  | CConditions
  | CCondition of int
  | CEffects
  | CExceptions
  | CScopes
  | CEvent of string

type rule_constr =
  | Suppressing of rule_constr_kind list
  | Causing     of rule_constr_kind list

type rule =
  | Obligation   of LexingInfo.t * Pattern.t * Pattern.t * rule_type * rule_constr list
  | Permission   of LexingInfo.t * Pattern.t * Pattern.t * rule_type * rule_constr list
  | Constitutive of LexingInfo.t * Pattern.t * Formula.t list
  | Exception    of LexingInfo.t * Pattern.t * Ref.t list
  | ExceptionC   of LexingInfo.t * Pattern.t * Ref.t list * Formula.t list
  | Scope        of LexingInfo.t * Pattern.t * Ref.t list

let pos_of_rule = function
  | Obligation   (pos, _, _, _, _) -> pos
  | Permission   (pos, _, _, _, _) -> pos
  | Constitutive (pos, _, _)       -> pos
  | Exception    (pos, _, _)       -> pos
  | ExceptionC   (pos, _, _, _)    -> pos
  | Scope        (pos, _, _)       -> pos

(* Statements and programs *)

type stmt =
  | SImport    of LexingInfo.t * import_format * string list
  | SSection   of LexingInfo.t * section_kind * string * string option
  | SRule      of LexingInfo.t * string option * (ident * TypeTerm.t) list * rule * string option
  | SEvent     of LexingInfo.t * event_type * ident * (ident * TypeTerm.t) list * Enftype.t * string option
  | SType      of LexingInfo.t * ident * (TypeTerm.t option) * string option
  | SFunction  of LexingInfo.t * ident * (ident * TypeTerm.t) list * TypeTerm.t * string option
  | SNote      of LexingInfo.t * string

let is_rule = function
  | SRule _ -> true
  | _       -> false

type signature = ident * (ident * Dom.tt) list

type prog = { stmts: stmt list }

(* Printing functions *)

let string_of_enftype enftype =
  if Enftype.is_internal enftype then
    "internal"
  else if Enftype.is_causable enftype then (
    if Enftype.is_suppressable enftype then
      "causable suppressable"
    else if Enftype.is_observable enftype then
      "causable observable"
    else
      "causable"
  )
  else if Enftype.is_suppressable enftype then
    "suppressable"
  else if Enftype.is_observable enftype then
    "observable"
  else if Enftype.is_absent enftype then
    "absent"
  else 
    assert false

let string_of_typed_idents (name, tt) =
  Printf.sprintf "%s : %s" name (Dom.tt_to_string tt)


let string_of_rule_type = function
  | Vanilla -> ""
  | Enforceable -> "enforceable "
  | Transparent -> "transparently enforceable "

let string_of_rule_constr_kind = function
  | CConditions -> "conditions"
  | CCondition i -> "condition[" ^ string_of_int i ^ "]"
  | CEffects -> "effects"
  | CExceptions -> "exceptions"
  | CScopes -> "scopes"
  | CEvent s -> s

let string_of_rule_constr = function
  | Suppressing cs -> "suppressing " ^ String.concat ~sep:", " (List.map cs ~f:string_of_rule_constr_kind)
  | Causing cs -> "causing " ^ String.concat ~sep:", " (List.map cs ~f:string_of_rule_constr_kind)
    
let string_of_rule_constrs rule_constrs =
  String.concat ~sep:", " (List.map ~f:string_of_rule_constr rule_constrs)

let verb_of_rule = function
  | Obligation _ -> "oblige"
  | Permission _ -> "permit"
  | Constitutive _ -> "constitute"
  | Exception _ 
    | ExceptionC _ -> "except"
  | Scope _ -> "scope"

let string_of_rule i rule =
  let open Pattern in
  let to_string (f: Formula.t) = Util.tabs (i+1) ^ Formula.to_string f in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:(fun f -> to_string f) f) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Util.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_imp_rule verb fp1 fp2 rcs rt =
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
  | Obligation (_, fp1, fp2, rt, rcs)
  | Permission (_, fp1, fp2, rt, rcs)
    -> string_of_imp_rule (verb_of_rule rule) fp1 fp2 rcs rt
  | Constitutive (_, fp, g)
    -> string_of_cons_rule (verb_of_rule rule) fp g
  | Exception (_, fp, references)
  | Scope (_, fp, references)
    -> string_of_exc_rule (verb_of_rule rule) fp references
  | ExceptionC (_, fp, references, g)
    -> string_of_excc_rule (verb_of_rule rule) fp references g

let string_of_args args i = 
    let string_of_arg (name, typ_alias) = 
      Printf.sprintf "%s%s : %s" (Util.tabs (i+1)) name (TypeTerm.value_to_string typ_alias)
    in
    String.concat ~sep:"\n" (List.map args ~f:string_of_arg)

let make_doc_string ds i = 
    let lines = String.split ~on:'\n' ds in
    let indented = List.map lines ~f:(fun l -> Util.tabs i ^ l) in
    Util.tabs (i + 1) ^ "\"\"\"" ^ String.concat ~sep:"\n" indented ^ Util.tabs i ^ "\"\"\"\n"

let string_of_import_format = function
  | ILex -> ""
  | IFormex -> " formex "
  | IAkomaNtoso -> " akomaNtoso "

let string_of_event_syntax = function
  | Functional -> " functional "
  | Variable -> " variable "
  | Standard -> ""

let string_of_event_type = function
  | Event (b, sy) -> (if b then "external " else "") ^ string_of_event_syntax sy ^ "event"
  | Predicate -> "predicate"
  | Exception -> "exception"

let string_of_type_fixes i = function
  | [] -> ""
  | type_fixes ->
     let f (ident, typ) = Printf.sprintf "%s : %s" ident (TypeTerm.value_to_string typ) in
     Printf.sprintf "%sfix\n%s%s\n"
       (Util.tabs i)
       (Util.tabs (i+1))
       (String.concat (List.map type_fixes ~f) ~sep:("\n" ^ Util.tabs (i+1)))

let string_of_stmt ?(i=0) =
  function
  | SImport (_, import_format, idents) ->
     Printf.sprintf "import %s%s"
       (string_of_import_format import_format)
       (String.concat ~sep:"." idents)
  | SSection (_, section_kind, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Util.tabs i)
       (string_of_section_kind section_kind)
       label
       (match title with Some title -> Printf.sprintf " \"%s\"" title | None -> "")
  | SRule (_, label, type_fixes, rule, doc_string) ->
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
  | SEvent (_, event_type, name, typed_args, pol, doc_string) ->
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
  | SType (_, name, typ, doc_string) ->
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
  | SFunction (_, name, typed_args, return_typ, doc_string) ->
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
  | SNote (_, text) -> "note \"" ^ text ^ "\""

let string_of_signature signature =
  match signature with
  | name, typed_idents ->
     Printf.sprintf "%s(%s)"
       name
       (String.concat ~sep:", " (List.map typed_idents ~f:string_of_typed_idents))
    
let string_of_prog prog =
  String.concat ~sep:"\n" (List.map prog.stmts ~f:string_of_stmt)
      
let print_prog prog =
  Stdio.printf "%s\n" (string_of_prog prog)

let prog_to_file filename prog =
  Out_channel.write_all filename ~data:(string_of_prog prog)

