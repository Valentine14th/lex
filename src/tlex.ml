open Core
open Lex

type trule =
  | TObligation   of Tformula.t list * Tformula.t list
  | TPermission   of Tformula.t list * Tformula.t list
  | TConstitutive of Tformula.t list * Tformula.t list
  | TException    of Tformula.t list * ident * Tformula.t

type 'a tannot =
  | TALex of 'a
  | TAFormex of string * 'a

let of_annot = function
  | TALex x -> x
  | TAFormex (_, x) -> x

type tstmt =
  | TSImport  of Lexing.position * string list * import_format
  | TSSection of section_kind * Label.t * string * string tannot option
  | TSRule    of Lexing.position * Label.t * (ident * Formula.TypeTerm.t) list * trule * rule_type * rule_constr list * string tannot option
  | TSEvent   of event_type * ident * (Lexing.position * ident * Formula.TypeTerm.t) list * pol * string option
  | TSType    of ident * Dom.tt * string option
  | TSFunction of ident * (ident * Formula.TypeTerm.t) list * Formula.TypeTerm.t * string option
  | TSNote    of string

type tevent = (Lexing.position * ident * Formula.TypeTerm.t) list * pol * string option
type tfunction = (ident * Formula.TypeTerm.t) list * Formula.TypeTerm.t * string option

type var_types = (ident, Formula.TypeTerm.t, Base.String.comparator_witness) Map.t

type tprog =
  {
    tstmts: tstmt list;
    taliases: (ident, Dom.tt * string option, Base.String.comparator_witness) Map.t; (* maps type aliases to their underlying type *)
    tevents: (ident, tevent, Base.String.comparator_witness) Map.t; (* maps event names to their definitions *)
    tfunctions: (ident, tfunction, Base.String.comparator_witness) Map.t;
    variables: (ident, var_types, Base.String.comparator_witness) Map.t; (* maps rule labels to variables used in section *)
    exceptions: (ident, (ident * Tformula.t) list, Base.String.comparator_witness) Map.t
  }

let tempty =
  {
    tstmts = [];
    taliases = Map.empty (module String);
    tevents = Map.empty (module String);
    tfunctions = Map.empty (module String);
    variables = Map.empty (module String); 
    exceptions = Map.empty (module String)
  }

let pol_map tprog =
  Map.map tprog.tevents ~f:(fun (_, pol, _) -> pol)

let add_tstmt tstmt tprog = { tprog with tstmts = tstmt::tprog.tstmts }

let add_talias name typ doc_string tprog pos =
  (* TODO: allow for overwriting/reusing existing type names *)
  let aliases =
    try Map.add_exn tprog.taliases ~key:name ~data:(typ, doc_string)
    with _ -> Util.type_error (Printf.sprintf "type alias %s already exists" name) pos
  in
  { tprog with taliases = aliases; tstmts = TSType (name, typ, doc_string)::tprog.tstmts }

let add_tevent event_type name args pol ds tprog pos =
  let event = (args, pol, ds) in
  (* TODO: allow for overwriting/reusing event names *)
  let events =
    try Map.add_exn tprog.tevents ~key:name ~data:event
    with _ -> Util.type_error (Printf.sprintf "event %s already exists" name) pos
  in
  { tprog with tevents = events; tstmts = TSEvent (event_type, name, args, pol, ds)::tprog.tstmts}

let add_tfunction name arg_types return_type ds tprog pos =
  let function_ = (arg_types, return_type, ds) in
  (* TODO: allow for overwriting/reusing event names *)
  let functions =
    try Map.add_exn tprog.tfunctions ~key:name ~data:function_
    with _ -> Util.type_error (Printf.sprintf "function %s already exists" name) pos
  in
  { tprog with tfunctions = functions; tstmts = TSFunction (name, arg_types, return_type, ds)::tprog.tstmts}

let add_vars vs name tprog pos =
  let variables =
    try Map.add_exn tprog.variables ~key:name ~data:vs
    with _ -> let err_msg = Printf.sprintf
                "rule label '%s' has already been defined"
                name in
      Util.label_error err_msg pos
  in
  { tprog with variables = variables }

let is_trule = function
  | TSRule _ -> true
  | _ -> false

let verb_of_trule = function
  | TObligation _ -> "oblige"
  | TPermission _ -> "permit"
  | TConstitutive _ -> "constitute"
  | TException _ -> "except"

let string_of_trule i trule =
  let to_string f =
    Etc.tabs (i+1) ^ Tformula.to_string f
  in
  let string_of_imp_rule verb f g =
    Printf.sprintf "%swhenever\n%s\n%s%s\n%s"
      (Etc.tabs i)
      (String.concat ~sep:"\n" (List.map ~f:to_string f))
      (Etc.tabs i)
      verb
      (String.concat ~sep:"\n" (List.map ~f:to_string g))
  in
  let string_of_exc_rule f ident =
    Printf.sprintf "%swhenever\n%s\n%sexcept \"%s\""
      (Etc.tabs i)
      (String.concat ~sep:"\n" (List.map ~f:to_string f))
      (Etc.tabs i)
      ident
  in
  match trule with
  | TObligation (f, g)
  | TPermission (f, g)
  | TConstitutive (f, g)
    -> string_of_imp_rule (verb_of_trule trule) f g
  | TException (f, ident, _) -> string_of_exc_rule f ident

let string_of_tstmt ?(i=0) =
  function
  | TSImport (_, idents, _) ->
     Printf.sprintf "import %s"
       (String.concat ~sep:"." idents)
  | TSSection (section_kind, _, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Etc.tabs i)
       (string_of_section_kind section_kind)
       label
       (match title with Some title -> Printf.sprintf ": \"%s\"" (of_annot title) | None -> "")
  | TSRule (_, label, type_fixes, rule, rule_type, rule_constrs, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string (of_annot s) i
          | None -> ""
      in
      Printf.sprintf "%srule%s\n%s%s\n%s%s%s%s"
        (Etc.tabs i)
        (Label.qualified_name label)
        (string_of_type_fixes (i+1) type_fixes)
        (string_of_trule (i+1) rule)
        (Etc.tabs i)
        (string_of_rule_type rule_type)
        (if List.is_empty rule_constrs then
          ""
        else
          Etc.tabs i ^ (string_of_rule_constrs rule_constrs))
       description
  | TSEvent (event_type, name, typed_args, pol, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
      Printf.sprintf "%s%s %s %s\n%s%s"
          (Etc.tabs i)
          (string_of_pol pol)
          (string_of_event_type event_type)
          name
          description
          (string_of_args typed_args i)
  | TSType (name, tt, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
     Printf.sprintf "%stype %s is %s%s"
       (Etc.tabs i) name (Dom.string_of_tt tt) description

  | TSFunction (name, typed_args, return_typ, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string s i
          | None -> ""
     in
     let f (ident, typ) =
       Printf.sprintf "%s : %s" ident (Formula.TypeTerm.value_to_string typ) in
     Printf.sprintf "%sfunction %s(%s) -> %s%s"
       (Etc.tabs i)
       name
       (String.concat ~sep:", " (List.map typed_args ~f))
       (Formula.TypeTerm.value_to_string return_typ)
       description
  | TSNote text -> "note \"" ^ text ^ "\""

let string_of_signature signature =
  match signature with
  | name, typed_idents ->
     Printf.sprintf "%s(%s)"
       name
       (String.concat ~sep:", " (List.map typed_idents ~f:string_of_typed_idents))
    
let string_of_tprog tprog =
  String.concat ~sep:"\n" (List.map tprog.tstmts ~f:string_of_tstmt)

let print_tprog tprog =
  Stdio.printf "%s\n" (string_of_tprog tprog)
