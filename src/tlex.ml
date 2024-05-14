open Core
open Lex

type trule =
  | TObligation   of (Lexing.position * Formula.t) list * (Lexing.position * Formula.t) list
  | TPermission   of (Lexing.position * Formula.t) list * (Lexing.position * Formula.t) list
  | TConstitutive of (Lexing.position * Formula.t) list * (Lexing.position * Formula.t) list
  | TException    of (Lexing.position * Formula.t) list * (Lexing.position * Label.t) list * Formula.t
  | TScope        of (Lexing.position * Formula.t) list * (Lexing.position * Label.t) list * Formula.t

type 'a tannot =
  | TALex of 'a
  | TAFormex of string * 'a

let of_annot = function
  | TALex x -> x
  | TAFormex (_, x) -> x

type tstmt =
  | TSImport  of Lexing.position * string list * import_format
  | TSSection of section_kind * Label.t * string * string tannot option
  | TSRule    of Lexing.position * int * Label.t * (ident * ident) list * trule * rule_type * rule_constr list * string tannot option
  | TSEvent   of event_type * ident * (Lexing.position * ident * ident) list * pol * string option
  | TSType    of ident * typ * string option
  | TSNote    of string

type tevent = (Lexing.position * ident * ident) list * pol * string option

type var_types = (ident, ident, Base.String.comparator_witness) Map.t

type tprog =
  {
    tstmts: tstmt list;
    taliases: (ident, typ * string option, Base.String.comparator_witness) Map.t; (* maps type aliases to their underlying type *)
    tevents: (ident, tevent, Base.String.comparator_witness) Map.t; (* maps event names to their definitions *)
    variables: (int, var_types, Int.comparator_witness) Map.t; (* maps rule labels to variables used in section *)
    rule_tree: Label.RuleTree.s;
    exception_predicates: (int, Formula.t, Int.comparator_witness) Map.t;
    scope_predicates: (int, Formula.t, Int.comparator_witness) Map.t;
  }

let tempty =
  {
    tstmts = [];
    taliases = Map.empty (module String);
    tevents = Map.empty (module String);
    variables = Map.empty (module Int); 
    rule_tree = Label.RuleTree.empty;
    exception_predicates = Map.empty (module Int);
    scope_predicates = Map.empty (module Int);
  }

let pol_map tprog =
  Map.map tprog.tevents ~f:(fun (_, pol, _) -> pol)

let add_tstmt tstmt tprog = { tprog with tstmts = tstmt::tprog.tstmts }

let add_talias name typ doc_string tprog pos =
  (* TODO: (potentially in the future) allow for overwriting/reusing existing type names *)
  let aliases =
    try Map.add_exn tprog.taliases ~key:name ~data:(typ, doc_string)
    with _ -> Util.type_error (Printf.sprintf "type alias %s already exists" name) pos
  in
  { tprog with taliases = aliases; tstmts = TSType (name, typ, doc_string)::tprog.tstmts }

let add_tevent event_type name args pol ds tprog pos =
  let event = (args, pol, ds) in
  (* TODO: (potentially in the future) allow for overwriting/reusing event names *)
  let events =
    try Map.add_exn tprog.tevents ~key:name ~data:event
    with _ -> Util.type_error (Printf.sprintf "event %s already exists" name) pos
  in
  { tprog with tevents = events; tstmts = TSEvent (event_type, name, args, pol, ds)::tprog.tstmts}

let add_exception i f refs tprog =
  { tprog with exception_predicates = Map.add_exn tprog.exception_predicates ~key:i ~data:f;
                rule_tree = Label.RuleTree.add_exception i refs tprog.rule_tree }

let add_scope i f refs tprog =
  { tprog with scope_predicates = Map.add_exn tprog.scope_predicates ~key:i ~data:f;
               rule_tree = Label.RuleTree.add_scope i refs tprog.rule_tree }

let set_labels pos label tprog =
  { tprog with rule_tree = Label.RuleTree.add_label pos tprog.rule_tree label }

let label_of_rule tprog id = Map.find_exn tprog.rule_tree.label_of_rule id

let add_vars id vs tprog =
  let variables = try Map.add_exn tprog.variables ~key:id ~data:vs
    with _ -> assert false
  in { tprog with variables = variables }

let add_rule pos rule_num label tprog =
  { tprog with rule_tree = Label.RuleTree.add_rule pos rule_num label tprog.rule_tree }

let add_section pos label tprog =
  { tprog with rule_tree = Label.RuleTree.add_section pos label tprog.rule_tree }

let is_trule = function
  | TSRule _ -> true
  | _ -> false

let verb_of_trule = function
  | TObligation _ -> "oblige"
  | TPermission _ -> "permit"
  | TConstitutive _ -> "constitute"
  | TException _ -> "except"
  | TScope _ -> "scope"

let string_of_trule i trule =
  let to_string f =
    Etc.tabs (i+1) ^ Formula.to_string f
  in
  let string_of_imp_rule verb f g =
    Printf.sprintf "%swhenever\n%s\n%s%s\n%s"
      (Etc.tabs i)
      (String.concat ~sep:"\n" (List.map ~f:to_string f))
      (Etc.tabs i)
      verb
      (String.concat ~sep:"\n" (List.map ~f:to_string g))
  in
  let string_of_ref_rule verb f trefs =
    let string_of_trefs labels =
      let refs = List.map labels ~f:Label.reference_of_label in
      String.concat ~sep:"\n" (List.map refs ~f:Lex.string_of_reference)
    in
    Printf.sprintf "%swhenever\n%s\n%s%s \"%s\""
      (Etc.tabs i)
      (String.concat ~sep:"\n" (List.map ~f:to_string f))
      (Etc.tabs i)
      verb
      (string_of_trefs trefs)
  in
  match trule with
  | TObligation (f, g)
  | TPermission (f, g)
  | TConstitutive (f, g)
    -> string_of_imp_rule (verb_of_trule trule) (List.map ~f:snd f) (List.map ~f:snd g)
  | TException (f, trefs, _)
  | TScope (f, trefs, _)
    -> string_of_ref_rule (verb_of_trule trule) (List.map ~f:snd f) (List.map ~f:snd trefs)

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
  | TSRule (_, _, label, type_fixes, rule, rule_type, rule_constrs, doc_string) ->
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
  | TSType (name, typ, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
     Printf.sprintf "type %s is %s%s"
       name (string_of_typ typ) description
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
