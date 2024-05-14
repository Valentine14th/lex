open Core

open Lex
open Tlex

type t =
  {
    tprog: tprog;
    label: Label.t;
    exceptions_first_pass: (int * Formula.t * (Lexing.position * Label.t) list) list;
    scopes_first_pass: (int * Formula.t * (Lexing.position * Label.t) list) list;
  }

let empty =
  {
    tprog = tempty;
    label = Label.empty;
    exceptions_first_pass = [];
    scopes_first_pass = [];
  }

let add_tstmt tstmt s =
  { s with tprog = Tlex.add_tstmt tstmt s.tprog }

let add_talias alias typ doc_string s pos =
  { s with tprog = Tlex.add_talias alias typ doc_string s.tprog pos }

let add_tevent event_type name args pol ds s pos =
  { s with tprog = Tlex.add_tevent event_type name args pol ds s.tprog pos }

let add_vars i vs s =
  { s with tprog = Tlex.add_vars i vs s.tprog }

let add_rule pos rule_num label s =
  { s with tprog = Tlex.add_rule pos rule_num label s.tprog }

let add_section pos label s =
  { s with tprog = Tlex.add_section pos label s.tprog }

let add_exception_first_pass i f refs s =
  { s with exceptions_first_pass = (i,f,refs)::s.exceptions_first_pass}

let add_scope_first_pass i f refs s =
  { s with scopes_first_pass = (i,f,refs)::s.scopes_first_pass}

let add_exception i f refs s =
  { s with tprog = Tlex.add_exception i f refs s.tprog; }

let add_scope i f refs s =
  { s with tprog = Tlex.add_scope i f refs s.tprog; }

let set_labels pos section_kind label s =
  let l = Label.set pos section_kind label s.label in
  { s with label = l; tprog = Tlex.set_labels pos l s.tprog }

let c = ref 0
let fresh () = incr c; !c

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
    | Some a' when (String.equal t_alias a') -> typed_vars
    | Some a' ->
      let err_msg = Printf.sprintf "Variable '%s' has type '%s' but was expected to have type '%s'" x a' t_alias in
      Util.type_error err_msg pos
    | None -> Map.add_exn typed_vars ~key:x ~data:t_alias
    end
  | Const c when type_check_constant c t -> typed_vars
  | Const c ->
    let err_msg = Printf.sprintf "Constant %s has type '%s' but expected '%s'"
      (string_of_const c) (string_of_typ (typ_of_const c)) (string_of_typ t)
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
let type_formulas t_vars fs s =
  let acc_function1 (p, f) = p, Formula.collect_predicates [] f in
  let acc_function2 l (pos, ps) = List.concat [l; List.map ~f:(fun x -> (pos, x)) ps] in
  let predicates = List.fold (List.map fs ~f:acc_function1) ~init:[] ~f:acc_function2 in
  let acc_function3 t_vars (pos, (n, ts)) =
    type_vars n ts t_vars pos s.tprog.tevents s.tprog.taliases
  in
  List.fold predicates ~init:t_vars ~f:acc_function3

let type_rule s pos = function
  | SRule (_, rule_id, type_fixes, rule, rule_type, rule_constrs, doc_string) -> begin
      let label' = Label.set_rule_id_force rule_id s.label in
      let _ = Label.valid_rule_label pos label' in
      let rule_num = fresh () in
      let section_kinds_are_in_order (k1, s1) (k2, s2) = match compare_section_kind k1 k2 with
        | i when i = 0 -> 
          let err_msg = Printf.sprintf "Section kind %s is defined more than once: '%s' and '%s'" (string_of_section_kind k1) s1 s2 in
          Util.reference_error err_msg pos
        | i when i < 0 -> 
          let err_msg = Printf.sprintf "Section kinds inside reference must be strictly 'decreasing', but '%s \"%s\"' is followed by '%s \"%s\"' which is at a greater level" 
            (string_of_section_kind k1) s1 (string_of_section_kind k2) s2
          in
          Util.reference_error err_msg pos
        | _ -> (k2, s2)
      in
      let decreasing_section_kinds (pos', r) = match r with
        | [], _ -> Util.reference_error "references must contain at least on reference" pos'
        | (r::rs), _ -> List.fold ~init:r ~f:section_kinds_are_in_order rs
      in
      let s, rule, fs = 
        match rule with
        | Exception (f, refs) ->
          let _ = List.map ~f:(decreasing_section_kinds) refs in
          let reference_labels = List.map ~f:(fun (pos',(rs, rule_id)) -> (pos', Label.set_rule_id rule_id (List.fold ~init:s.label ~f:(fun acc (level, name) -> Label.set pos level (name, None) acc) rs))) refs in
          let p_name = "Exception" ^ string_of_int rule_num in
          let vars = Set.elements (Set.union_list (module String) (List.map f ~f:(fun (_,f') -> Formula.fv f'))) in
          let terms = List.map vars ~f:(fun x -> Formula.Term.Var x) in
          let pred = Formula.predicate p_name terms in
          let s' = add_exception_first_pass rule_num pred reference_labels s in
          s', TException (f, reference_labels, pred), f
        | Scope (f, refs) ->
          let _ = List.map ~f:decreasing_section_kinds refs in
          let reference_labels = List.map ~f:(fun (pos',(rs, rule_id)) -> (pos', Label.set_rule_id rule_id (List.fold ~init:s.label ~f:(fun acc (level, name) -> Label.set pos level (name, None) acc) rs))) refs in
          let p_name = "Scope" ^ string_of_int rule_num in
          let vars = Set.elements (Set.union_list (module String) (List.map f ~f:(fun (_,f') -> Formula.fv f'))) in
          let terms = List.map vars ~f:(fun x -> Formula.Term.Var x) in
          let pred = Formula.predicate p_name terms in
          let s' = add_scope_first_pass rule_num pred reference_labels s in
          s', TScope (f, reference_labels, pred), f
        | Obligation (f1, f2) -> s, TObligation (f1, f2), List.concat [f1; f2]
        | Permission (f1, f2) -> s, TPermission (f1, f2), List.concat [f1; f2]
        | Constitutive (f1, f2) -> s, TConstitutive (f1, f2), List.concat [f1; f2]
      in
      let t_vars = Map.of_alist_exn (module String) type_fixes in
      let vars = type_formulas t_vars fs s in
      let s' = add_vars rule_num vars s in
      let s'' = add_rule pos rule_num label' s' in
      let doc_string' = Option.map doc_string ~f:(fun x -> TALex x) in
      add_tstmt (TSRule (pos, rule_num, label', type_fixes, rule, rule_type, rule_constrs, doc_string')) s''
    end
  | _ -> assert false

let type_stmt s = function
  | SImport (pos, import_format, idents) -> add_tstmt (TSImport (pos, idents, import_format)) s
  | SSection (pos, section_kind, label_description, title) ->
     let s = set_labels pos section_kind (label_description, title) s in
     let title' = Option.map title ~f:(fun x -> TALex x) in
     let s' = add_section pos s.label s in
     add_tstmt (TSSection (section_kind, s.label, label_description, title')) s'
  | SRule (pos, _, _, _, _, _, _) as rule -> type_rule s pos rule
  | SEvent (pos, event_type, name, args, pol, ds) -> add_tevent event_type name args pol ds s pos
  | SType (pos, name, typ, doc_string) -> add_talias name typ doc_string s pos
  | SNote (_, text) -> add_tstmt (TSNote text) s
    
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

let merge_type_maps m1 m2 label = Map.merge m1 m2 ~f:(fun ~key:k -> function
  | `Both (a1, a2) when String.equal a1 a2 -> Some a1
  | `Both (a1, a2) -> let err_msg = Printf.sprintf
        "Variable '%s' has type '%s' in rule '%s', but was expected to have type '%s'"
        k a1 label a2
      in Util.type_error err_msg Lexing.dummy_pos
  | `Left t
  | `Right t -> Some t)

(* let check_var_types tprog = tprog.variables *)
let check_var_types tprog =
  let var_equivalence_classes = Label.RuleTree.rules_with_shared_variables tprog.rule_tree in
  let f0 acc' key =
      let var_types = Map.find_exn tprog.variables key in
      let label = Label.RuleTree.string_of_rule_idx tprog.rule_tree key in
      merge_type_maps var_types acc' label
  in
  let f1 keys = (keys, Set.fold keys ~init:(Map.empty (module String)) ~f:f0) in
  let updated_vars = List.map var_equivalence_classes ~f:f1 in
  let f2 v acc key = Map.add_exn acc ~key:key ~data:v in
  let f3 m (keys, v) = Set.fold keys ~init:m ~f:(f2 v) in
  let vars = List.fold ~init:(Map.empty (module Int)) ~f:f3 updated_vars in
  vars

let do_type _ prog =
  (* First pass: type statements *)
  let s = List.fold prog.stmts ~init:empty ~f:type_stmt in
  (* Second pass: exceptions *)
  let tprog' = List.fold s.exceptions_first_pass ~init:s.tprog ~f:(fun acc (i,f,refs) -> Tlex.add_exception i f refs acc) in
  let tprog'' = List.fold s.scopes_first_pass ~init:tprog' ~f:(fun acc (i,f,refs) -> Tlex.add_scope i f refs acc) in
  (* TODO: check that variables in exceptions have the same type as in the original rules *)
  (* let vars = check_var_types tprog'' in *)
  {
    tstmts = List.rev tprog''.tstmts;
    taliases = tprog''.taliases;
    tevents = tprog''.tevents;
    (* variables = vars; *)
    variables = tprog''.variables;
    rule_tree = tprog''.rule_tree;
    exception_predicates = tprog''.exception_predicates;
    scope_predicates = tprog''.scope_predicates
  }
