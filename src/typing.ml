open Core

open Lex
open Tlex

type t =
  {
    tprog: tprog;
    label: Label.t;
    labelconvention: (module Label.LabelConvention);
    exceptions: (string * Label.t * Lexing.position * Formula.t) list;
    rule_labels: (string, Label.t, Base.String.comparator_witness) Map.t
  }

let empty =
  {
    tprog = tempty;
    label = Label.empty;
    labelconvention = (module Label.StandardConvention);
    exceptions = [];
    rule_labels = Map.empty (module String)
  }

let add_tstmt tstmt s =
  { s with tprog = Tlex.add_tstmt tstmt s.tprog }

let add_talias alias typ doc_string s pos =
  { s with tprog = Tlex.add_talias alias typ doc_string s.tprog pos }

let add_tevent event_type name args pol ds s pos =
  { s with tprog = Tlex.add_tevent event_type name args pol ds s.tprog pos }

let add_vars vs ls s pos =
  { s with tprog = Tlex.add_vars vs ls s.tprog pos }

let add_rule_labels rule_name label s pos =
  try { s with rule_labels = Map.add_exn s.rule_labels ~key:rule_name ~data:label }
  with _ -> let err_msg = Printf.sprintf
                  "rule label '%s' has already been defined"
                  rule_name
    in Util.label_error err_msg pos

let add_exception pos f ident s =
  { s with exceptions = (ident, s.label, pos, f)::s.exceptions }

let set_labels pos section_kind label s =
  let module Convention = (val s.labelconvention : Label.LabelConvention) in
  let set = Convention.convention.set in
  { s with label = set pos section_kind label s.label }

let c = ref 0
let fresh () = incr c; string_of_int !c

let type_check_constant c t = match (c, t) with
  | Dom.Int _, TInt
  | Dom.Str _, TString
  | Dom.Float _, TFloat -> true
  | _, _ -> false

let string_of_const = function
  | Dom.Int i -> string_of_int i
  | Dom.Str s -> s
  | Dom.Float f -> string_of_float f

let typ_of_const = function
  | Dom.Int _ -> TInt
  | Dom.Str _ -> TString
  | Dom.Float _ -> TFloat

let type_var (pos, v, t_alias) typed_vars taliases =
  let t = match Map.find taliases t_alias with
    | Some (typ, _) -> typ
    | None -> let err_msg =
        Printf.sprintf "Type alias '%s' is undefined" t_alias in
      Util.type_error err_msg pos
  in
  match v with
  | Formula.Term.Var x -> begin match Map.find typed_vars x with
    | Some a' ->
      if (String.equal t_alias a') then typed_vars
      else let err_msg = Printf.sprintf
          "Variable '%s' has type '%s' but was expected to have type '%s'"
          x a' t_alias
        in
        Util.type_error err_msg pos
    | None -> Map.add_exn typed_vars ~key:x ~data:t_alias
    end
  | Const c -> if type_check_constant c t then  typed_vars
    else let err_msg = 
        Printf.sprintf
        "Constant %s has type '%s' but expected '%s'"
        (string_of_const c)
        (string_of_typ (typ_of_const c))
        (string_of_typ t)
      in
      Util.type_error err_msg pos

let type_vars event_name vars t_vars pos tevents taliases =
  let args = match Map.find tevents event_name with
      | Some (args, _, _) -> args
      | None -> let err_msg = Printf.sprintf
                              "Event '%s' is undefined"
                              event_name
                in Util.type_error err_msg pos
    in
    let acc_function t_vars (pos, _, type_alias) v = type_var (pos, v, type_alias) t_vars taliases in
    match List.fold2 args vars ~init:t_vars ~f:acc_function with
      | Ok t_vars' -> t_vars'
      | Unequal_lengths ->
        let err_msg = Printf.sprintf
          "Number of arguments doesn't match for event '%s'"
          event_name
        in
        Util.type_error err_msg pos

(* TODO: currently the error location `pos` is the beginning of the rule
         it might be helpful to have pointers inside the rule,
         e.g. to the predicate name, or variable names
         this would require changes to formaula.ml *)
let type_formulas t_vars fs s pos =
  let acc_function1 f = Formula.collect_predicates [] f in
  let acc_function2 l ps = List.concat [l; ps] in
  let predicates = List.fold (List.map fs ~f:acc_function1) ~init:[] ~f:acc_function2 in
  let acc_function3 t_vars (n, ts) =
    type_vars n ts t_vars pos s.tprog.tevents s.tprog.taliases
  in
  List.fold predicates ~init:t_vars ~f:acc_function3

let type_rule s pos = function
  | SRule (_, rule_id, type_fixes, rule, rule_type, rule_constrs, doc_string) -> begin
      let label' = Label.set_rule_id rule_id s.label in
      let module Convention = (val s.labelconvention : Label.LabelConvention) in
      let qualified_name = Convention.convention.qualified_name in
      let label_name = Label.valid_rule_label pos label'; qualified_name label' in
      let s, rule, fs = 
        match rule with
        | Exception (f, ident) ->
          let p_name = "Exception" ^ fresh () in
          let vars = Set.elements (Set.union_list (module String) (List.map f ~f:Formula.fv)) in
          let terms = List.map vars ~f:(fun x -> Formula.Term.Var x) in
          let pred = Formula.predicate p_name terms in
          let s' = add_exception pos pred ident s in
          s', TException (f, ident, pred), f
        | Obligation (f1, f2) -> s, TObligation (f1, f2), List.concat [f1; f2]
        | Permission (f1, f2) -> s, TPermission (f1, f2), List.concat [f1; f2]
        | Constitutive (f1, f2) -> s, TConstitutive (f1, f2), List.concat [f1; f2]
      in
      let t_vars = Map.of_alist_exn (module String) type_fixes in
      let vars = type_formulas t_vars fs s pos in
      let s' = add_vars vars label_name s pos in
      let s'' = add_rule_labels label_name label' s' pos in
      let doc_string' = Option.map doc_string ~f:(fun x -> TALex x) in
      add_tstmt (TSRule (pos, label', type_fixes, rule, rule_type, rule_constrs, doc_string')) s''
    end
  | _ -> assert false

let type_stmt s = function
  | SImport (pos, import_format, idents) -> add_tstmt (TSImport (pos, idents, import_format)) s
  | SSection (pos, section_kind, label, title) ->
     let s = set_labels pos section_kind (label, title) s in
     let title' = Option.map title ~f:(fun x -> TALex x) in
     add_tstmt (TSSection (section_kind, s.label, label, title')) s
  | SRule (pos, _, _, _, _, _, _) as rule -> type_rule s pos rule
  | SEvent (pos, event_type, name, args, pol, ds) -> add_tevent event_type name args pol ds s pos
  | SType (pos, name, typ, doc_string) -> add_talias name typ doc_string s pos
  | SNote (_, text) -> add_tstmt (TSNote text) s
    
let resolve_exception_identifiers s =
  let append_exception rule_labels m (ident, label, pos, f) =
    let module Convention = (val s.labelconvention : Label.LabelConvention) in
    let get_full_name = Convention.convention.get_full_name in
    let qualified_name = Convention.convention.qualified_name in
    let name = get_full_name ident label pos rule_labels in
    Map.add_multi m ~key:name ~data:(qualified_name label, f)
  in
  List.fold s.exceptions ~init:(Map.empty (module String)) ~f:(append_exception s.rule_labels)

let update_var_ts_with_exceptions vars exceptions =
  let type_exception ~key:name ~data:es vs =
    let existing_vars = try Map.find_exn vs name with _ -> assert false in
    let merge_var_types types (exception_rule_name, _) =
      let exception_vars = try Map.find_exn vs exception_rule_name with _ -> assert false in
      Map.merge types exception_vars ~f:(fun ~key:k -> function
          | `Both (a1, a2) ->
            if String.equal a1 a2 then Some a1
              else let err_msg =
                  Printf.sprintf
                  "Variable '%s' has type '%s' in rule '%s', but has type '%s' in exception '%s' for this rule"
                  k a1 name a2 exception_rule_name
                in Util.type_error err_msg Lexing.dummy_pos
          | `Left t
          | `Right t -> Some t)
    in
    let new_vars = List.fold es ~init:existing_vars ~f:merge_var_types in
    let exception_rules = try List.map (Map.find_exn exceptions name) ~f:fst with _ -> assert false in
    let m = List.fold exception_rules ~init:vs ~f:(fun acc value -> Map.update acc value ~f:(fun _ -> new_vars)) in
    Map.update m name ~f:(fun _ -> new_vars)
  in Map.fold exceptions ~init:vars ~f:type_exception

let do_type _ prog labelconvention =
  (* First pass: type statements *)
  let init = {empty with labelconvention = labelconvention} in
  let s = List.fold prog.stmts ~init:init ~f:type_stmt in
  (* Second pass: exceptions *)
  let exceptions = resolve_exception_identifiers s in
  let variables = update_var_ts_with_exceptions s.tprog.variables exceptions in
  {
    tstmts = List.rev s.tprog.tstmts;
    taliases = s.tprog.taliases;
    tevents = s.tprog.tevents;
    variables = variables;
    exceptions = exceptions;
    labelconvention = s.tprog.labelconvention
  }


