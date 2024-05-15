open Core

open Formula.TypeTerm
open Formula.Term
open Lex
open Tlex

type t =
  {
    tprog: tprog;
    label: Label.t;
    exceptions: (string * Label.t * Lexing.position * Tformula.t) list;
    rule_labels: (string, Label.t, Base.String.comparator_witness) Map.t
  }

let empty =
  {
    tprog = tempty;
    label = Label.empty;
    exceptions = [];
    rule_labels = Map.empty (module String)
  }

let add_tstmt tstmt s =
  { s with tprog = Tlex.add_tstmt tstmt s.tprog }

let add_talias alias typ doc_string s pos =
  { s with tprog = Tlex.add_talias alias typ doc_string s.tprog pos }

let add_tfunction name arg_types return_type doc_string s pos =
  { s with tprog = Tlex.add_tfunction name arg_types return_type doc_string s.tprog pos }

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
  { s with label = Label.set pos section_kind label s.label }

let c = ref 0
let fresh () = incr c; string_of_int !c

let type_check_constant c t = match (c, t) with
  | Dom.Int _, Dom.TInt
  | Dom.Str _, TStr
  | Dom.Float _, TFloat
  | Dom.Bool _, TBool
  | Dom.Time _, TTime -> true
  | Dom.Money m, TMoney c -> String.equal (Money.currency m) c
  | _, _ -> false

let rec type_term tfunctions typed_vars pos v t_alias =
  (*let t = match Map.find taliases t_alias with
    | Some (typ, _) -> typ
    | None -> let err_msg =
                Printf.sprintf "Type alias '%s' is undefined" (value_to_string t_alias) in
              Util.type_error err_msg pos
  in*)
  match v with
  | Var x ->
     begin match Map.find typed_vars x, t_alias with
     | Some a', _ -> (typed_vars, Tformula.term (TVar x) a')
     | None, Some t -> (Map.add_exn typed_vars ~key:x ~data:t, Tformula.term (TVar x) t)
     | _, _ -> let err_msg = Printf.sprintf "Cannot infer the type of variable %s" x in
               Util.type_error err_msg pos
     end
  | Const c -> (typed_vars, Tformula.term (TConst c) (TypeConst (Dom.tt_of_domain c)))
  | App (f_name, trms) ->
     begin
       let f (typed_vars, trms) trm (arg_name, arg_type) =
         let typed_vars, trm = type_term tfunctions typed_vars pos trm (Some arg_type) in
         if Formula.TypeTerm.equal trm.tt arg_type then
           (typed_vars, trm :: trms)
         else
           let err_msg =
             Printf.sprintf
               "Type mismatch for argument %s of function %s: expected '%s', found '%s'"
               arg_name f_name (Formula.TypeTerm.value_to_string trm.tt)
               (Formula.TypeTerm.value_to_string arg_type) in
           Util.type_error err_msg pos
       in
       match Map.find tfunctions f_name with
       | Some (arg_types, return_type, _) ->
          begin match List.fold2 trms arg_types ~init:(typed_vars, []) ~f with
          | Ok (typed_vars, trms) ->
             (typed_vars, Tformula.term (TApp (f_name, List.rev trms)) return_type)
          | Unequal_lengths ->
             let err_msg = Printf.sprintf "Function %s expects %d arguments, found %d"
                             f_name (List.length arg_types) (List.length trms) in
             Util.type_error err_msg pos
          end
       | None -> let err_msg =
                   Printf.sprintf "Function '%s' is undefined" f_name in
                 Util.type_error err_msg pos
     end
  | Unop (UNot, trm) ->
     begin
       let typed_vars, trm = type_term tfunctions typed_vars pos trm (Some (TypeConst TBool)) in
       if Formula.TypeTerm.equal trm.tt (TypeConst TBool) then
         (typed_vars, Tformula.term (TUnop (UNot, trm)) (TypeConst TBool))
       else
         let err_msg = Printf.sprintf "Negation (!) expects type TBool, found '%s'"
                         (Formula.TypeTerm.value_to_string trm.tt) in
         Util.type_error err_msg pos
     end
  | Unop (USub, trm) ->
     begin
       let typed_vars, trm = type_term tfunctions typed_vars pos trm None in
       if Formula.TypeTerm.supports_usub trm.tt then
         (typed_vars, trm)
       else
         let err_msg = Printf.sprintf "Unary minus (-) expects TInt, TFloat, TSpan, or TMoney, found '%s'"
                         (Formula.TypeTerm.value_to_string trm.tt) in
         Util.type_error err_msg pos
     end
  | Binop _ -> assert false

let type_terms event_name trms t_vars pos tevents tfunctions =
  let args = match Map.find tevents event_name with
    | Some (args, _, _) -> args
    | None -> let err_msg = Printf.sprintf
                              "Event '%s' is undefined"
                              event_name
              in Util.type_error err_msg pos
  in
  let acc_function (t_vars, trms) (pos, arg_name, type_alias) trm =
    let t_vars, trm = type_term tfunctions t_vars pos trm (Some type_alias) in
    let ty = Tformula.Term.(trm.tt) in
    if Formula.TypeTerm.equal ty type_alias then
      (t_vars, trm :: trms)
    else
      let err_msg = Printf.sprintf "Type mismatch for argument %s of event %s: expected '%s', found '%s'"
                      arg_name event_name (Formula.TypeTerm.value_to_string type_alias)
                      (Formula.TypeTerm.value_to_string ty) in
      Util.type_error err_msg pos
  in
  match List.fold2 args trms ~init:(t_vars, []) ~f:acc_function with
  | Ok (t_vars', trms') -> (t_vars', List.rev trms')
  | Unequal_lengths ->
     let err_msg = Printf.sprintf
                     "Number of arguments doesn't match for event '%s'"
                     event_name
     in
     Util.type_error err_msg pos

let rec type_formula s pos t_vars = function
  | Formula.TT -> t_vars, Tformula.TTT
  | FF -> t_vars, TFF
  | EqConst (x, y) ->
     begin
       let t_vars, x' = type_term s.tfunctions t_vars pos x None in
       let t_vars, y' = type_term s.tfunctions t_vars pos y None in
       if Formula.TypeTerm.equal x'.tt y'.tt then
         (t_vars, TEqConst (x', y'))
       else
         let err_msg = Printf.sprintf "Ill-typed argument types in equality: '%s' vs '%s'"
                         (Formula.TypeTerm.to_string x'.tt) (Formula.TypeTerm.to_string y'.tt) in
         Util.type_error err_msg pos
     end
  | Predicate (event_name, trms) ->
     let t_vars, trms = type_terms event_name trms t_vars pos s.tevents s.tfunctions in
     (t_vars, TPredicate (event_name, trms))
  | Neg f ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TNeg f
  | And (side, fs) ->
     let t_vars, fs = List.fold_map fs ~init:t_vars ~f:(type_formula s pos) in
     t_vars, TAnd (side, fs)
  | Or (side, fs) ->
     let t_vars, fs = List.fold_map fs ~init:t_vars ~f:(type_formula s pos) in
     t_vars, TOr (side, fs)
  | Imp (side, f, g) ->
     let t_vars, f = type_formula s pos t_vars f in
     let t_vars, g = type_formula s pos t_vars g in
     t_vars, TImp (side, f, g)
  | Iff (side, side', f, g) ->
     let t_vars, f = type_formula s pos t_vars f in
     let t_vars, g = type_formula s pos t_vars g in
     t_vars, TIff (side, side', f, g)
  | Exists (x, f) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TExists (x, f)
  | Forall (x, f) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TForall (x, f)
  | Prev (i, f) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TPrev (i, f)
  | Next (i, f) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TNext (i, f)
  | Once (i, f) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TOnce (i, f)
  | Eventually (i, f) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TEventually (i, f)
  | Historically (i, f) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, THistorically (i, f)
  | Always (i, f) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TAlways (i, f)
  | Since (side, i, f, g) ->
     let t_vars, f = type_formula s pos t_vars f in
     let t_vars, g = type_formula s pos t_vars g in
     t_vars, TSince (side, i, f, g)
  | Until (side, i, f, g) ->
     let t_vars, f = type_formula s pos t_vars f in
     let t_vars, g = type_formula s pos t_vars g in
     t_vars, TUntil (side, i, f, g)
  | Type (f, ty) ->
     let t_vars, f = type_formula s pos t_vars f in
     t_vars, TType (f, ty)

(* TODO: currently the error location `pos` is the beginning of the rule
         it might be helpful to have pointers inside the rule,
         e.g. to the predicate name, or variable names
         this would require changes to formaula.ml *)
(*let type_formulas t_vars fs s pos =
  let acc_function1 f = Formula.collect_predicates [] f in
  let acc_function2 l ps = List.concat [l; ps] in
  let predicates = List.fold (List.map fs ~f:acc_function1) ~init:[] ~f:acc_function2 in
  let acc_function3 t_vars (n, ts) =
    type_terms n ts t_vars pos s.tprog.tevents s.tprog.tfunctions
  in
  List.fold predicates ~init:t_vars ~f:acc_function3*)

let type_rule s pos = function
  | SRule (_, rule_id, type_fixes, rule, rule_type, rule_constrs, doc_string) -> begin
      let label' = Label.set_rule_id rule_id s.label in
      let label_name = Label.valid_rule_label pos label'; Label.qualified_name label' in
      let t_vars = Map.of_alist_exn (module String) type_fixes in
      let s, t_vars, rule = 
        match rule with
        | Exception (f, ident) ->
           let p_name = "Exception" ^ fresh () in
           let t_vars, f = List.fold_map f ~init:t_vars ~f:(type_formula s.tprog pos) in
           let vars = Set.elements (Set.union_list (module String) (List.map f ~f:Tformula.fv)) in
           let var_term_of_ident x =
             Tformula.Term.{ trm = Tformula.Term.TVar x; tt = Map.find_exn t_vars x } in
           let terms = List.map vars ~f:var_term_of_ident in
           let pred = Tformula.tpredicate p_name terms in
           let s' = add_exception pos pred ident s in
          s', t_vars, TException (f, ident, pred)
        | Obligation (f1, f2) ->
           let t_vars, f1 = List.fold_map f1 ~init:t_vars ~f:(type_formula s.tprog pos) in
           let t_vars, f2 = List.fold_map f2 ~init:t_vars ~f:(type_formula s.tprog pos) in
           s, t_vars, TObligation (f1, f2)
        | Permission (f1, f2) ->
           let t_vars, f1 = List.fold_map f1 ~init:t_vars ~f:(type_formula s.tprog pos) in
           let t_vars, f2 = List.fold_map f2 ~init:t_vars ~f:(type_formula s.tprog pos) in
           s, t_vars, TPermission (f1, f2)
        | Constitutive (f1, f2) ->
           let t_vars, f1 = List.fold_map f1 ~init:t_vars ~f:(type_formula s.tprog pos) in
           let t_vars, f2 = List.fold_map f2 ~init:t_vars ~f:(type_formula s.tprog pos) in
           s, t_vars, TConstitutive (f1, f2)
      in
      let s' = add_vars t_vars label_name s pos in
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
  | SFunction (pos, name, arg_types, return_type, doc_string) -> add_tfunction name arg_types return_type doc_string s pos
  | SNote (_, text) -> add_tstmt (TSNote text) s
    
let resolve_exception_identifiers s =
  let append_exception rule_labels m (ident, label, pos, f) =
    let name = Label.get_full_name ident label pos rule_labels in
    Map.add_multi m ~key:name ~data:(Label.qualified_name label, f)
  in
  List.fold s.exceptions ~init:(Map.empty (module String)) ~f:(append_exception s.rule_labels)

let update_var_ts_with_exceptions vars exceptions =
  let type_exception ~key:name ~data:es vs =
    let existing_vars = try Map.find_exn vs name with _ -> assert false in
    let merge_var_types types (exception_rule_name, _) =
      let exception_vars = try Map.find_exn vs exception_rule_name with _ -> assert false in
      Map.merge types exception_vars ~f:(fun ~key:k -> function
          | `Both (a1, a2) ->
            if Formula.TypeTerm.equal a1 a2 then Some a1
              else let err_msg =
                  Printf.sprintf
                  "Variable '%s' has type '%s' in rule '%s', but has type '%s' in exception '%s' for this rule"
                  k (Formula.TypeTerm.to_string a1) name (Formula.TypeTerm.to_string a2) exception_rule_name
                in Util.type_error err_msg Lexing.dummy_pos
          | `Left t
          | `Right t -> Some t)
    in
    let new_vars = List.fold es ~init:existing_vars ~f:merge_var_types in
    let exception_rules = try List.map (Map.find_exn exceptions name) ~f:fst with _ -> assert false in
    let m = List.fold exception_rules ~init:vs ~f:(fun acc value -> Map.update acc value ~f:(fun _ -> new_vars)) in
    Map.update m name ~f:(fun _ -> new_vars)
  in Map.fold exceptions ~init:vars ~f:type_exception

let do_type _ prog =
  (* First pass: type statements *)
  let s = List.fold prog.stmts ~init:empty ~f:type_stmt in
  (* Second pass: exceptions *)
  let exceptions = resolve_exception_identifiers s in
  let variables = update_var_ts_with_exceptions s.tprog.variables exceptions in
  {
    tstmts = List.rev s.tprog.tstmts;
    taliases = s.tprog.taliases;
    tevents = s.tprog.tevents;
    tfunctions = s.tprog.tfunctions;
    variables = variables;
    exceptions = exceptions
  }


