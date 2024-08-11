open Core
open Lex

type tpattern =
  | TPPresent
  | TPEventually of Interval.t
  | TPAlways of Interval.t
  | TPUntil of Interval.t * Tformula.t
  | TPOnce of Interval.t
  | TPHistorically of Interval.t
  | TPSince of Interval.t * Tformula.t

type trule =
  | TObligation   of (Lexing.position * Tformula.t) list * tpattern * (Lexing.position * Tformula.t) list * tpattern * rule_type * rule_constr list
  | TPermission   of (Lexing.position * Tformula.t) list * tpattern * (Lexing.position * Tformula.t) list * tpattern * rule_type * rule_constr list
  | TConstitutive of (Lexing.position * Tformula.t) list * tpattern * (Lexing.position * Tformula.t) list
  | TException    of (Lexing.position * Tformula.t) list * tpattern * (Lexing.position * Label.t * Lex.reference) list * Tformula.t
  | TExceptionC   of (Lexing.position * Tformula.t) list * tpattern * (Lexing.position * Label.t * Lex.reference) list * Tformula.t * (Lexing.position * Tformula.t) list
  | TScope        of (Lexing.position * Tformula.t) list * tpattern * (Lexing.position * Label.t * Lex.reference) list * Tformula.t

type trule_type = TRTObligation | TRTPermission | TRTConstitutive | TRTException | TRTExceptionC | TRTScope

type trule_compilation =
  | TCImplication   of int * trule_type * Lexing.position * (Lexing.position * Tformula.t) list * tpattern * (Lexing.position * Tformula.t) list * (Lexing.position * Tformula.t) list * (Lexing.position * Tformula.t) list * tpattern * rule_type * rule_constr list
  | TCDefinition    of int * trule_type * Lexing.position * (Lexing.position * Tformula.t) list * tpattern * (Lexing.position * Tformula.t) list * (Lexing.position * Tformula.t) list * (Lexing.position * Label.t * Lex.reference) list * Tformula.t
  | TCDefinitionDis of (int, (int * trule_type * Lexing.position * (Lexing.position * Tformula.t) list  * tpattern* (Lexing.position * Tformula.t) list * (Lexing.position * Tformula.t) list * Tformula.t list), Int.comparator_witness) Map.t * Tformula.t
                             (* rule_id, trule_type, rule pos,     f1,                                  , pattern,   exceptions,                           scopes,                           variable renaiming *)

type 'a tannot =
  | TALex of 'a
  | TAFormex of string * 'a

let of_annot = function
  | TALex x -> x
  | TAFormex (_, x) -> x

type tstmt =
  | TSImport  of Lexing.position * string list * import_format
  | TSSection of section_kind * Label.t * string * string tannot option
  | TSRule    of Lexing.position * int * Label.t * (ident * Formula.TypeTerm.t) list * trule * string tannot option
  | TSEvent   of event_type * ident * (Lexing.position * ident * Formula.TypeTerm.t) list * pol * string option
  | TSType    of ident * Formula.TypeTerm.t option * string option
  | TSFunction of ident * (ident * Formula.TypeTerm.t) list * Formula.TypeTerm.t * string option
  | TSNote    of string

type tevent = event_type * (Lexing.position * ident * Formula.TypeTerm.t) list * pol * string option
type tfunction = (ident * Formula.TypeTerm.t) list * Formula.TypeTerm.t * string option

type var_types = (ident, Formula.TypeTerm.t, Base.String.comparator_witness) Map.t

type tprog =
  {
    tstmts: tstmt list;
    taliases: (ident, Formula.TypeTerm.t option * string option, Base.String.comparator_witness) Map.t;
    (* maps type aliases to their underlying type *)
    tevents: (ident, tevent, Base.String.comparator_witness) Map.t;
    (* maps event names to their definitions *)
    tfunctions: (ident, tfunction, Base.String.comparator_witness) Map.t;
    (* maps function names to their definitions *)
    variables: (int, var_types, Int.comparator_witness) Map.t;
    (* maps rule labels to variables used in section *)
    rule_tree: Label.RuleTree.s;
    exception_predicates: (int, Tformula.t, Int.comparator_witness) Map.t;
    scope_predicates: (int, Tformula.t, Int.comparator_witness) Map.t;
  }

let tempty =
  {
    tstmts = [];
    taliases = Map.empty (module String);
    tevents = Builtin.events_map;
    tfunctions = Builtin.functions_map;
    variables = Map.empty (module Int); 
    rule_tree = Label.RuleTree.empty;
    exception_predicates = Map.empty (module Int);
    scope_predicates = Map.empty (module Int);
  }

let trule_map tprog =
  List.fold tprog.tstmts ~init:(Map.empty (module Int))
    ~f:(fun acc -> function
        | TSRule (_, i, _, _, rule, _) -> Map.add_exn acc ~key:i ~data:rule
        | _ -> acc)

let pol_map tprog =
  Map.map tprog.tevents ~f:(fun (_, _, pol, _) -> pol)

let add_tstmt tstmt tprog = { tprog with tstmts = tstmt::tprog.tstmts }

let add_talias name typ doc_string tprog pos =
  (* TODO: (potentially in the future) allow for overwriting/reusing existing type names *)
  let aliases =
    try Map.add_exn tprog.taliases ~key:name ~data:(typ, doc_string)
    with _ -> Util.type_error (Printf.sprintf "type alias %s already exists" name) pos
  in
  { tprog with taliases = aliases; tstmts = TSType (name, typ, doc_string)::tprog.tstmts }

let add_tevent event_type name args pol ds tprog pos =
  let event = (event_type, args, pol, ds) in
  (* TODO: (potentially in the future) allow for overwriting/reusing event names *)
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

(*let add_vars vs name tprog pos =
  let variables =
    try Map.add_exn tprog.variables ~key:name ~data:vs
    with _ -> let err_msg = Printf.sprintf
                "rule label '%s' has already been defined"
                name in
      Util.label_error err_msg pos
  in
  { tprog with variables = variables }*)

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
  | TException _
    | TExceptionC _ -> "except"
  | TScope _ -> "scope"


let string_of_tpattern = function
  | TPPresent -> ""
  | TPEventually i -> " eventually " ^ Interval.to_string i 
  | TPAlways i -> " always in the future " ^ Interval.to_string i 
  | TPUntil (i, f) -> " eventually delaying if " ^ Tformula.to_string f ^ " " ^ Interval.to_string i
  | TPOnce i -> " once " ^ Interval.to_string i
  | TPHistorically i -> " always in the past " ^ Interval.to_string i
  | TPSince (i, f) -> " always since " ^ Tformula.to_string f ^ " " ^ Interval.to_string i

let predicates_of_tpattern = function
  | TPPresent
  | TPEventually _
  | TPAlways _
  | TPHistorically _
    | TPOnce _ -> []
  | TPUntil (_, f)
    | TPSince (_, f) -> Tformula.collect_tpredicates [] f

let string_of_trule i trule =
  let to_string f = Etc.tabs (i+1) ^ Tformula.to_string f in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:(fun (_,f') -> to_string f') f) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Etc.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_imp_rule verb f p g q rcs rt =
    Etc.tabs i     ^ "whenever" ^ string_of_tpattern p ^ "\n"
    ^ string_of_formula_list f ^ "\n"
    ^ Etc.tabs i   ^ verb     ^ string_of_tpattern q ^ "\n"
    ^ string_of_formula_list g
    ^ Etc.tabs i ^ string_of_rule_type rt (* TODO: check that this prints the rule_type correctly *)
    ^ (if List.is_empty rcs then "" (* TODO: check that this prints the rule_constr list correctly *)
      else Etc.tabs i ^ (string_of_rule_constrs rcs))
  in
  let string_of_cons_rule verb f p g =
    Etc.tabs i     ^ "whenever" ^ string_of_tpattern p ^ "\n"
    ^ string_of_formula_list f ^ "\n"
    ^ Etc.tabs i   ^ verb      ^ "\n"
    ^ string_of_formula_list g
  in
  let string_of_ref_rule verb f p refs =
    (* let refs = List.map trefs ~f:Label.reference_of_label in *)
    Etc.tabs i     ^ "whenever" ^ string_of_tpattern p ^ "\n"
    ^ string_of_formula_list f ^ "\n"
    ^ Etc.tabs i   ^ verb                             ^ "\n"
    ^ String.concat ~sep:"\n" (List.map refs ~f:Lex.string_of_reference)
  in
  let string_of_refc_rule verb f p refs g =
    Etc.tabs i     ^ "whenever"  ^ string_of_tpattern p ^ "\n"
    ^ string_of_formula_list f ^ "\n"
    ^ Etc.tabs i   ^ verb
    ^ String.concat ~sep:"\n" (List.map refs ~f:Lex.string_of_reference)
    ^ Etc.tabs i   ^ "constitute"
    ^ string_of_formula_list g
  in
  match trule with
  | TObligation (f, p, g, q, rt, rcs)
  | TPermission (f, p, g, q, rt, rcs)
    -> string_of_imp_rule (verb_of_trule trule) f p g q rcs rt
  | TConstitutive (f, p, g)
    -> string_of_cons_rule (verb_of_trule trule) f p g
  | TException (f, p, trefs, _)
  | TScope (f, p, trefs, _)
    -> string_of_ref_rule (verb_of_trule trule) f p (List.map ~f:(fun (_,_,x) -> x) trefs)
  | TExceptionC (f, p, trefs, _, g)
    -> string_of_refc_rule (verb_of_trule trule) f p (List.map ~f:(fun (_,_,x) -> x) trefs) g

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
  | TSRule (_, _, label, type_fixes, rule, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string (of_annot s) i
          | None -> ""
      in
      Printf.sprintf "%srule%s\n%s%s\n%s"
        (Etc.tabs i)
        (Label.qualified_name label)
        (string_of_type_fixes (i+1) type_fixes)
        (string_of_trule (i+1) rule)
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
          | None -> "" in
      let typ_string =
       match typ with
       | Some tt -> " is " ^ Formula.TypeTerm.value_to_string tt
       | None -> "" in
     Printf.sprintf "%stype %s%s%s"
       (Etc.tabs i) name typ_string description
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

let string_of_var_types var_types =
  let f (k, v) = k ^ " : " ^ Formula.TypeTerm.to_string v in
  "[" ^ String.concat ~sep:", " (List.map (Map.to_alist var_types) ~f) ^ "]"

let print_tprog tprog =
  Stdio.printf "%s\n" (string_of_tprog tprog)


let unpack_functional tevents trm' trm =
  match Tformula.Term.(trm.trm) with
  | Tformula.Term.TApp (f, trms) ->
     (match Map.find tevents f with
      | Some (Event (_, Functional), _, _, _) ->
         Some (f, trms @ [trm'])
      | _ -> None)
  | _ -> None

let unpack_variable tevents trm' trm =
  match Tformula.Term.(trm.trm) with
  | Tformula.Term.TVar x ->
     (match Map.find tevents x with
      | Some (Event (_, Variable), _, _, _) ->
         Some (x, [trm'])
      | _ -> None)
  | _ -> None

let unpack_special_eq tevents trm trm' =
  List.find_map
    [unpack_functional tevents trm trm';
     unpack_functional tevents trm' trm;
     unpack_variable tevents trm trm';
     unpack_variable tevents trm' trm]
    ~f:(fun x -> x)

