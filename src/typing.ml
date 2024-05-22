open Core

open Formula.TypeTerm
open Formula.Term
open Lex
open Tlex

type t =
  {
    tprog: tprog;
    label: Label.t;
    exceptions_first_pass: (int * Tformula.t * (Lexing.position * Label.t) list) list;
    scopes_first_pass: (int * Tformula.t * (Lexing.position * Label.t) list) list;
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

let add_tfunction name arg_types return_type doc_string s pos =
  { s with tprog = Tlex.add_tfunction name arg_types return_type doc_string s.tprog pos }

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
  | Dom.Int _, Dom.TInt
  | Dom.Str _, TStr
  | Dom.Float _, TFloat
  | Dom.Bool _, TBool
  | Dom.Time _, TTime -> true
  | Dom.Money m, TMoney c -> String.equal (Money.currency m) c
  | _, _ -> false

let type_unot = function
  | TypeConst Dom.TBool
    | TypeConst Dom.TInt as ty -> Some ty
  | _ -> None

let type_usub = function
  | TypeConst Dom.TInt
    | TypeConst Dom.TFloat
    | TypeConst Dom.TSpan
    | TypeConst (Dom.TMoney _) as ty -> Some ty
  | _ -> None

let type_badd = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt 
    | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    | TypeConst Dom.TFloat, TypeConst Dom.TInt
    | TypeConst Dom.TStr, TypeConst Dom.TStr
    | TypeConst Dom.TTime, TypeConst Dom.TSpan
    | TypeConst Dom.TSpan, TypeConst Dom.TSpan as args
    -> Some (fst args)
  | TypeConst (Dom.TMoney c), TypeConst (Dom.TMoney c')
       when String.equal c c'
    -> Some (TypeConst (Dom.TMoney c))
  | TypeConst Dom.TInt, TypeConst Dom.TFloat
    | TypeConst Dom.TSpan, TypeConst Dom.TTime as args
    -> Some (snd args)
  | _ -> None

let type_bsub = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt 
    | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    | TypeConst Dom.TFloat, TypeConst Dom.TInt
    | TypeConst Dom.TTime, TypeConst Dom.TSpan
    | TypeConst Dom.TSpan, TypeConst Dom.TSpan as args
    -> Some (fst args)
  | TypeConst (Dom.TMoney c), TypeConst (Dom.TMoney c')
       when String.equal c c'
    -> Some (TypeConst (Dom.TMoney c))
  | TypeConst Dom.TInt, TypeConst Dom.TFloat
    -> Some (TypeConst Dom.TFloat)
  | _ -> None

let type_bmul = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt
    | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    | TypeConst Dom.TInt, TypeConst Dom.TFloat
    | TypeConst Dom.TInt, TypeConst Dom.TSpan
    | TypeConst Dom.TFloat, TypeConst Dom.TSpan as args
    -> Some (snd args)
  | TypeConst Dom.TInt, TypeConst (Dom.TMoney c)
    | TypeConst Dom.TFloat, TypeConst (Dom.TMoney c)
    | TypeConst (Dom.TMoney c), TypeConst Dom.TInt
    | TypeConst (Dom.TMoney c), TypeConst Dom.TFloat
    -> Some (TypeConst (Dom.TMoney c))
  | TypeConst Dom.TFloat, TypeConst Dom.TInt
    | TypeConst Dom.TSpan, TypeConst Dom.TInt
    | TypeConst Dom.TSpan, TypeConst Dom.TFloat as args 
    -> Some (fst args)
  | _ -> None

let type_bdiv = function
  | TypeConst Dom.TInt, TypeConst Dom.TFloat as args
    -> Some (snd args)
  | TypeConst Dom.TInt, TypeConst Dom.TInt 
    | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    | TypeConst Dom.TFloat, TypeConst Dom.TInt
    | TypeConst Dom.TSpan, TypeConst Dom.TInt
    | TypeConst Dom.TSpan, TypeConst Dom.TFloat as args
    -> Some (fst args)
  | TypeConst (Dom.TMoney c), TypeConst Dom.TInt
    | TypeConst (Dom.TMoney c), TypeConst Dom.TFloat
    -> Some (TypeConst (Dom.TMoney c))
  | _ -> None

let type_bpow = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt
    -> Some (TypeConst Dom.TInt)
  | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    -> Some (TypeConst Dom.TFloat)
  | _ -> None

let type_band = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt
    -> Some (TypeConst Dom.TInt)
  | TypeConst Dom.TBool, TypeConst Dom.TBool
    -> Some (TypeConst Dom.TBool)
  | _ -> None

let type_beq (ty, ty') =
  if Formula.TypeTerm.equal ty ty' then
    Some ty
  else
    None

let type_blt = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt
  | TypeConst Dom.TFloat, TypeConst Dom.TFloat
  | TypeConst Dom.TInt, TypeConst Dom.TFloat
  | TypeConst Dom.TFloat, TypeConst Dom.TInt
  | TypeConst Dom.TTime, TypeConst Dom.TTime
  | TypeConst Dom.TSpan, TypeConst Dom.TSpan
    -> Some (TypeConst Dom.TBool)
  | TypeConst (Dom.TMoney c), TypeConst (Dom.TMoney c') when String.equal c c'
    -> Some (TypeConst Dom.TBool)
  | _ -> None

let rec type_term tfunctions taliases typed_vars pos v t_alias =
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
         let typed_vars, trm = type_term tfunctions taliases typed_vars pos trm (Some arg_type) in
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
  | Unop (op, trm) ->
     begin
       let typed_vars, trm = type_term tfunctions taliases typed_vars pos trm None in
       let f_op = match op with
         | UNot -> type_unot
         | USub -> type_usub in
       match f_op trm.tt with
       | Some ty -> (typed_vars, Tformula.term (TUnop (UNot, trm)) ty)
       | None ->
         let err_msg = Printf.sprintf "Unary (!) expects type TBool, found '%s'"
                         (Formula.TypeTerm.value_to_string trm.tt) in
         Util.type_error err_msg pos
     end
  | Binop (trm, op, trm') ->
     begin
       let typed_vars, trm  = type_term tfunctions taliases typed_vars pos trm None in
       let typed_vars, trm' = type_term tfunctions taliases typed_vars pos trm' None in
       let f_op = match op with
         | BAdd -> type_badd
         | BSub -> type_bsub
         | BMul -> type_bmul
         | BDiv -> type_bdiv
         | BPow -> type_bpow
         | BAnd | BOr | BXor -> type_band
         | BEq | BNeq -> type_beq
         | BLt | BLeq | BGt | BGeq -> type_blt
       in
       match f_op (trm.tt, trm'.tt) with
       | Some ty -> (typed_vars, Tformula.term (TBinop (trm, op, trm')) ty)
       | None ->
          let err_msg = Printf.sprintf "The types '%s' and '%s' are not applicable to binary plus (+)"
                          (Formula.TypeTerm.value_to_string trm.tt)
                          (Formula.TypeTerm.value_to_string trm'.tt) in
          Util.type_error err_msg pos
     end

let type_terms event_name trms t_vars pos tevents tfunctions taliases =
  let args = match Map.find tevents event_name with
    | Some (_, args, _, _) -> args
    | None -> let err_msg = Printf.sprintf
                              "Event '%s' is undefined"
                              event_name
              in Util.type_error err_msg pos
  in
  let acc_function (t_vars, trms) (_, arg_name, type_alias) trm =
    let t_vars, trm = type_term tfunctions taliases t_vars pos trm (Some type_alias) in
    let ty = Tformula.Term.(trm.tt) in
    match Formula.TypeTerm.lub ty type_alias taliases with
    | Some tt -> let trm = { trm with tt } in (t_vars, trm :: trms)
    | None ->
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
       let t_vars, x' = type_term s.tfunctions s.taliases t_vars pos x None in
       let t_vars, y' = type_term s.tfunctions s.taliases t_vars pos y None in
       if Formula.TypeTerm.equal x'.tt y'.tt then
         (t_vars, TEqConst (x', y'))
       else
         let err_msg = Printf.sprintf "Ill-typed argument types in equality: '%s' vs '%s'"
                         (Formula.TypeTerm.to_string x'.tt) (Formula.TypeTerm.to_string y'.tt) in
         Util.type_error err_msg pos
     end
  | Predicate (event_name, trms) ->
     let t_vars, trms = type_terms event_name trms t_vars pos s.tevents s.tfunctions s.taliases in
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

let type_formula_pos s pos acc (p, f) =
  let acc, f = type_formula s.tprog pos acc f in
  (acc, (p, f))

let type_pattern s pos t_vars = function
  | PPresent -> t_vars, TPPresent
  | PEventually i -> t_vars, TPEventually i
  | PAlways i -> t_vars, TPAlways i
  | PUntil (i, f) -> let t_vars, f = type_formula s pos t_vars f in t_vars, TPUntil (i, f)
  | POnce i -> t_vars, TPOnce i
  | PHistorically i -> t_vars, TPHistorically i
  | PSince (i, f) -> let t_vars, f = type_formula s pos t_vars f in t_vars, TPSince (i, f)

let type_rule s pos = function
  | SRule (_, rule_id, type_fixes, rule, rule_type, rule_constrs, doc_string) -> begin
      let label' = Label.set_rule_id_force rule_id s.label in
      let _ = Label.valid_rule_label pos label' in
      let t_vars = Map.of_alist_exn (module String) type_fixes in
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
      let s, rule = 
        match rule with
        | Exception (f, p, refs) ->
          let _ = List.map ~f:(decreasing_section_kinds) refs in
          let reference_labels = List.map ~f:(fun (pos',(rs, rule_id)) -> (pos', Label.set_rule_id rule_id (List.fold ~init:s.label ~f:(fun acc (level, name) -> Label.set pos level (name, None) acc) rs))) refs in
          let p_name = "Exception" ^ string_of_int rule_num in
          let t_vars, f = List.fold_map f ~init:t_vars ~f:(type_formula_pos s pos) in
          let vars = Set.elements (Set.union_list (module String)
                                     (List.map f ~f:(fun (_, f) -> Tformula.fv f))) in
          let var_term_of_ident x =
            Tformula.Term.{ trm = Tformula.Term.TVar x; tt = Map.find_exn t_vars x } in
          let terms = List.map vars ~f:var_term_of_ident in
          let pred = Tformula.tpredicate p_name terms in
          let s' = add_exception_first_pass rule_num pred reference_labels s in
          let _, p = type_pattern s.tprog pos t_vars p in
          s', TException (f, p, reference_labels, pred)
        | Scope (f, p, refs) ->
          let _ = List.map ~f:decreasing_section_kinds refs in
          let reference_labels = List.map ~f:(fun (pos',(rs, rule_id)) -> (pos', Label.set_rule_id rule_id (List.fold ~init:s.label ~f:(fun acc (level, name) -> Label.set pos level (name, None) acc) rs))) refs in
          let p_name = "Scope" ^ string_of_int rule_num in
          let t_vars, f = List.fold_map f ~init:t_vars ~f:(type_formula_pos s pos) in
          let vars = Set.elements (Set.union_list (module String)
                                     (List.map f ~f:(fun (_, f) -> Tformula.fv f))) in
          let var_term_of_ident x =
            Tformula.Term.{ trm = Tformula.Term.TVar x; tt = Map.find_exn t_vars x } in
          let terms = List.map vars ~f:var_term_of_ident in
          let pred = Tformula.tpredicate p_name terms in
          let s' = add_scope_first_pass rule_num pred reference_labels s in
          let _, p = type_pattern s.tprog pos t_vars p in
          s', TScope (f, p, reference_labels, pred)
        | Obligation (f1, p, f2, q) ->
           let t_vars, f1 = List.fold_map f1 ~init:t_vars ~f:(type_formula_pos s pos) in
           let t_vars, f2 = List.fold_map f2 ~init:t_vars ~f:(type_formula_pos s pos) in
           let t_vars, p = type_pattern s.tprog pos t_vars p in
           let _, q = type_pattern s.tprog pos t_vars q in
           s, TObligation (f1, p, f2, q)
        | Permission (f1, p, f2, q) ->
           let t_vars, f1 = List.fold_map f1 ~init:t_vars ~f:(type_formula_pos s pos) in
           let t_vars, f2 = List.fold_map f2 ~init:t_vars ~f:(type_formula_pos s pos) in
           let t_vars, p = type_pattern s.tprog pos t_vars p in
           let _, q = type_pattern s.tprog pos t_vars q in
           s, TPermission (f1, p, f2, q)
        | Constitutive (f1, p, f2) ->
           let t_vars, f1 = List.fold_map f1 ~init:t_vars ~f:(type_formula_pos s pos) in
           let t_vars, f2 = List.fold_map f2 ~init:t_vars ~f:(type_formula_pos s pos) in
           let _, p = type_pattern s.tprog pos t_vars p in
           s, TConstitutive (f1, p, f2)
      in
      let s' = add_vars rule_num t_vars s in
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
  | SFunction (pos, name, arg_types, return_type, doc_string) -> add_tfunction name arg_types return_type doc_string s pos
  | SNote (_, text) -> add_tstmt (TSNote text) s
    
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

let merge_type_maps m1 m2 label = Map.merge m1 m2 ~f:(fun ~key:k -> function
  | `Both (a1, a2) when Formula.TypeTerm.equal a1 a2 -> Some a1
  | `Both (a1, a2) -> let err_msg = Printf.sprintf
        "Variable '%s' has type '%s' in rule '%s', but was expected to have type '%s'"
        k (Formula.TypeTerm.to_string a1) label (Formula.TypeTerm.to_string a2)
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
    tfunctions = tprog''.tfunctions;
    variables = tprog''.variables;
    rule_tree = tprog''.rule_tree;
    exception_predicates = tprog''.exception_predicates;
    scope_predicates = tprog''.scope_predicates
  }
