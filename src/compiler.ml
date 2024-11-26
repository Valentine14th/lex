open Core

open Term
open Eformula
open Lex
open Elex
open Clex

let debug_compiler = ref false
let debug msg = if !debug_compiler then Errors.debug_print ~f_name:(Some "compiler.ml") msg else ignore msg

(* TODO: constants inside of predicates do not
   actually introduce an unnamed variable for the
   "exception" predicate...
   i.e. being able to create a fresh name for variables
   is not needed*)
let c = ref 0
let fresh_var () = incr c; "_v" ^ string_of_int !c


let rec merge tts tts' =
  match tts, tts' with
  | [], _ -> tts'
  | tt :: tts, tt' :: tts' when Dom.tt_equal tt tt' -> tt :: (merge tts tts')
  | tt :: tts, tts' -> tt :: (merge tts tts')

let merge_all =
  List.fold_left ~init:[] ~f:merge

let normalize kvss =
  List.sort kvss ~compare:(fun (k, _) (k', _) -> String.compare k k')

let compile_tt = function
  | Dom.TInt -> Dom.TInt
  | TStr -> TStr
  | TFloat -> TFloat
  | TBool -> TInt
  | TTime -> TFloat
  | TSpan -> TFloat
  | TMoney _ -> TInt

let compile_dom = function
  | Dom.Int i -> Dom.Int i
  | Str s -> Str s
  | Float f -> Float f
  | Bool b -> Int (if b then 1 else 0)
  | Time t -> Float (Lextime.Time.to_float t)
  | Span _ -> assert false
  | Money (Money.M (a, _)) -> Int a

let prefix_tt = function
  | Dom.TInt -> "i"
  | TStr -> "s"
  | TFloat -> "f"
  | _ -> assert false

let compile_unop = function
  | USub -> "usub"
  | UNot -> "not"

let compile_binop = function
  | BAdd -> "add"
  | BSub -> "sub"
  | BMul -> "mul"
  | BDiv -> "div"
  | BPow -> "pow"
  | BAnd -> "and"
  | BOr  -> "or"
  | BXor -> "xor"
  | BEq  -> "eq"
  | BNeq -> "neq"
  | BLt  -> "lt"
  | BLeq -> "leq"
  | BGt  -> "gt"
  | BGeq -> "geq"

(*
let rec compile_term aliases term =
  let compile_unop tt f =
    prefix_tt tt ^ compile_unop f in
  let compile_binop tt tt' f =
    let p  = prefix_tt tt in
    let p' = prefix_tt tt' in
    let prefix = if String.equal p p' then p else p ^ p' in
    prefix ^ compile_binop f in
  let trm = 
    match Term.(term.trm) with
    | Term.TVar v -> Term.TVar v
    | Term.TConst d -> Term.TConst (compile_dom d)
    | Term.TApp (f, terms) -> Term.TApp (f, List.map ~f:(compile_term aliases) terms)
    | Term.TUnop (op, term) ->
       let f = compile_unop (compile_tt (Formula.TypeTerm.eval_default aliases TInt term.tt)) op in
       Term.TApp (f, [compile_term aliases term])
    | Term.TBinop (term, op, term') ->
       let f = compile_binop
                 (compile_tt (Formula.TypeTerm.eval_default aliases TInt term.tt))
                 (compile_tt (Formula.TypeTerm.eval_default aliases TInt term'.tt)) op in
       Term.TApp (f, [compile_term aliases term; compile_term aliases term'])
  in { term with trm }
 *)

let compile_epattern ?(use_pattern_for_enf=false) ?(only_pattern=false) ?(enftype=EnfType.Cau) (f: Eformula.t) = function
  | EPPresent -> f
  | EPEventually i -> { f = EEventually (i, Interval.is_bounded i, f); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
  | EPAlways i -> { f = EAlways (i, Interval.is_bounded i, f); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
  | EPUntil (i, g) ->
    if use_pattern_for_enf then { f = EUntil (LR, i, Interval.is_bounded i, g, f); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
    else if only_pattern then   { f = EUntil (L, i, Interval.is_bounded i, g, f); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
    else                        { f = EUntil (R, i, Interval.is_bounded i, g, f); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
  | EPOnce i -> { f = EOnce (i, f); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
  | EPHistorically i -> { f = EHistorically (i, f); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
  | EPSince (i, g) ->
    if use_pattern_for_enf then { f = ESince (LR, i, f, g); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
    else if only_pattern then   { f = ESince (R, i, f, g); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }
    else                        { f = ESince (L, i, f, g); variable_instantiations=[]; enftype; id = 0; pos = LexingInfo.dummy }

let compile_eformulas ~f fs = f fs

let compile_epformula ?(use_pattern_for_enf=false) ?(only_pattern=false) ?(enftype=EnfType.Cau) ~f (epf: epformula): Eformula.t =
  compile_epattern ~use_pattern_for_enf ~only_pattern ~enftype (compile_eformulas ~f epf.fs) epf.p

let compile_lhs ?(sup_constr=None) ?(cau_constr=None) (enftype: EnfType.t) pf ex sc =
  match enftype with
  | Cau ->
    let enf_cau = Option.value_exn cau_constr in
    begin match enf_cau with
    | EClhsAll enf_pformula_cau ->
      let ex_neg = List.map ex ~f:(fun x -> make (ENeg x) Cau [] 0 x.pos) in
      let f = begin match enf_pformula_cau with
        | ECpfFormulas -> compile_epformula ~f:tbigcauconj pf
        | ECpfPformula -> compile_epformula ~use_pattern_for_enf:true ~f:tbigcauconj pf
        | ECpfPattern -> compile_epformula ~use_pattern_for_enf:true ~only_pattern:true ~f:tbignonconj pf
      end in
      tbigcauconj (f :: ex_neg @ sc)
    end
  | Sup ->
    let enf_sup = Option.value_exn sup_constr in
    begin match enf_sup with
    | ESlhsSPformula enf_pformula_sup ->
      begin match enf_pformula_sup with
      | ESpfFormula i ->
        let cpf = compile_epformula ~enftype:Sup ~f:(tbigsupconj i) pf in (* this is used for enforcement *)
        let ex_neg = List.map ex ~f:(fun x -> make (ENeg x) Sup [] 0 x.pos) in
        let ex_neg_and_scope = tbignonconj (ex_neg @ sc) in (* this is not used for enforcement *)
        make (EAnd (L, [cpf; ex_neg_and_scope])) Sup [] 0 LexingInfo.dummy
      | ESpfPformula i ->
        let cpf = compile_epformula ~use_pattern_for_enf:true ~f:(tbigsupconj i) pf in
        let ex_neg = List.map ex ~f:(fun x -> make (ENeg x) Sup [] 0 x.pos) in
        let ex_neg_and_scope = tbignonconj (ex_neg @ sc) in
        make (EAnd (L, [cpf; ex_neg_and_scope])) Sup [] 0 LexingInfo.dummy
      | ESpfPattern ->
        let cpf = compile_epformula ~use_pattern_for_enf:true ~only_pattern:true ~f:tbignonconj pf in
        let ex_neg = List.map ex ~f:(fun x -> make (ENeg x) Sup [] 0 x.pos) in
        let ex_neg_and_scope = tbignonconj (ex_neg @ sc) in
        make (EAnd (L, [cpf; ex_neg_and_scope])) Sup [] 0 LexingInfo.dummy
      end
    | ESlhsCException i ->
      let cpf = compile_epformula ~f:tbignonconj pf in
      let ex_neg = List.map ex ~f:(fun x -> make (ENeg x) Sup [] 0 x.pos) in
      let ex_neg_sup = tbigsupconj i ex_neg in
      let ex_neg_and_scope = make (EAnd (L, ex_neg_sup::sc )) Sup [] 0 LexingInfo.dummy in
      make (EAnd (R, [cpf; ex_neg_and_scope])) Sup [] 0 LexingInfo.dummy
    | ESlhsSScope i ->
      let cpf = compile_epformula ~f:tbignonconj pf in
      let ex_neg = List.map ex ~f:(fun x -> make (ENeg x) Sup [] 0 x.pos) in
      let sc_sup = tbigsupconj i sc in
      let ex_neg_and_scope = make (EAnd (L, sc_sup::ex_neg )) Sup [] 0 LexingInfo.dummy in
      make (EAnd (R, [cpf; ex_neg_and_scope])) Sup [] 0 LexingInfo.dummy
    end
  (* TODO: how to handle other cases (if at all) ? *)
  | _ -> assert false

(* let compile_let_binding (pf: epformula) (ex_and_sc: Eformula.t list) pred : Eformula.t * Eformula.t = *)
let compile_let_binding ?(quantifier=true) (f: Eformula.t) pred : Eformula.t * Eformula.t =
  match pred with
  | { f = EPredicate (p_name, trms, event_type); _} ->
    let process_term fs (trm: TTerm.t) = match trm.trm with
      | ETerm.TVar _ -> fs, trm
      | _ ->
        let v = ETerm.{
          trm = ETerm.TVar (fresh_var ());
          tt = trm.tt;
          pos = LexingInfo.dummy
        } in
        let eq = ETerm.{
          trm = ETerm.TBinop (v, Term.BEq, trm);
          tt = TypeTerm.TypeConst Dom.TBool;
          pos = LexingInfo.dummy
        } in
        let ef = {
          f = EEqConst (eq, (Dom.Bool true, LexingInfo.dummy));
          variable_instantiations = [];
          enftype = EnfType.Obs;
          id = 0;
          pos = LexingInfo.dummy
        } in
        ef :: fs, v
    in
    let fs', trms = List.fold_map trms ~init:[] ~f:process_term in
    let fs = f :: List.rev fs' in
    let lhs = { pred with f = EPredicate (p_name, trms, event_type) } in
    let rhs = tbigcauconj fs in
    let vars = Map.keys (Eformula.fv rhs) in
    let rhs = if quantifier then tbigcauexists vars rhs else rhs in
    (lhs, rhs)
  | _ -> assert false

let compile_edisjunct ?(cau_constr=None) ?(sup_constr=None) (enftype: EnfType.t) ed: Eformula.t =
  (* let renaming = List.map2 ed.params_new ed.params_original ~f:(fun t1 t2 -> eeqconst t1 t2) in *)
  (* TODO: implement variable renaming using 'gets' operator *)
  let param_names = List.map ed.params_new ~f:(fun t -> match t.trm with
    | ETerm.TVar v -> v
    | _ -> assert false) in
  let renaming = List.zip_exn param_names ed.params_original in
  match enftype with
  | Cau ->
    let c = Option.value_exn cau_constr in
    let compiled = compile_lhs ~cau_constr:(Some c) Cau ed.pf ed.exceptions ed.scopes in
    { compiled with variable_instantiations = renaming }
  | Sup ->
    let c = Option.value_exn sup_constr in
    let compiled = compile_lhs ~sup_constr:(Some c) Sup ed.pf ed.exceptions ed.scopes in
    { compiled with variable_instantiations = renaming }
  | Non ->
    let ex_neg = List.map ed.exceptions ~f:(fun x -> make (ENeg x) Non [] 0 x.pos) in
    let compiled = tbignonconj (compile_epformula ~f:(tbignonconj) ed.pf :: ex_neg @ ed.scopes) in
    { compiled with variable_instantiations = renaming }
  | _ -> assert false

let compile_let_rule = function
  | ECDefinition (_, _, _, pf, ex, sc, _, g, enf_constr) ->
    begin match enf_constr with
    | Some (ESd enf_sup_lhs) ->
      let f = compile_lhs ~sup_constr:(Some enf_sup_lhs) Sup pf ex sc in
      compile_let_binding ~quantifier:false f g
    | Some (ECd enf_cau_lhs) ->
      let f = compile_lhs ~cau_constr:(Some enf_cau_lhs) Cau pf ex sc in
      compile_let_binding ~quantifier:false f g
    | None ->
      let ex_neg = List.map ex ~f:(fun x -> make (ENeg x) Non [] 0 x.pos) in
      let pf_comp = compile_epformula ~f:(tbignonconj) pf in
      let f = tbignonconj (pf_comp :: ex_neg @ sc) in
      compile_let_binding ~quantifier:false f g
    end
  | ECDefinitionDis (edisjuncts, g, enf_constr) ->
    begin match enf_constr with
    | Some (ECdd (idx, enf_cau_lhs)) -> 
      let rhs_list =
        let aux ~key:j ~data:d =
          if idx = j then compile_edisjunct ~cau_constr:(Some enf_cau_lhs) Cau d
          else compile_edisjunct Non d
        in
        Map.mapi edisjuncts ~f:aux |> Map.data
      in
      let rhs = tbigcaudisj idx rhs_list in
      compile_let_binding rhs g
    | Some (ESdd enf_sup_lhs_list) ->
      let rhs = tbignondisj (List.map2_exn (Map.data edisjuncts) enf_sup_lhs_list
        ~f:(fun d c -> compile_edisjunct ~sup_constr:(Some c) Sup d)) in
      compile_let_binding rhs g
    | None ->
      let rhs = tbignondisj (Map.data (Map.map edisjuncts ~f:(compile_edisjunct EnfType.Non)))  in
      compile_let_binding rhs g
    end
  | _ -> assert false

let compile_imp (f1: Eformula.t) (f2: Eformula.t) (s: Side.t) =
  let vars = List.fold [f2; f1] ~init:(Map.empty (module String)) ~f:(fun map f -> fv ~map f)
             |> Map.keys in
  make (EAlways
    (Interval.full,
     true,
     tbigcauforall vars
       ((make (EImp (s, f1, f2)) Cau [] 0 LexingInfo.dummy))))
    Cau [] 0 LexingInfo.dummy

let compile_imp_rule = function
  | ECImplication (_, _, _, pf1, ex, sc, pf2, _, _, Some enf_info) ->
    begin match enf_info with
    | ESciLhs enf_sup ->
      let lhs = compile_lhs ~sup_constr:(Some enf_sup) Sup pf1 ex sc in
      let rhs = compile_epformula ~f:tbignonconj pf2 in
      compile_imp lhs rhs L
    | ECciRhs enf_cau ->
      let cpf = compile_epformula ~f:tbignonconj pf1 in
      let ex_neg = List.map ex ~f:(fun x -> make (ENeg x) Sup [] 0 x.pos) in
      let ex_neg_and_scope = tbignonconj (ex_neg @ sc) in (* this is not used for enforcement *)
      let lhs = make (EAnd (R, [cpf; ex_neg_and_scope])) Sup [] 0 LexingInfo.dummy in
      begin match enf_cau with
      | ECpfFormulas ->
        let rhs = compile_epformula ~f:tbigcauconj pf2 in
        compile_imp lhs rhs R
      | ECpfPformula ->
        let rhs = compile_epformula ~use_pattern_for_enf:true ~f:tbigcauconj pf2 in
        compile_imp lhs rhs R
      | ECpfPattern ->
        let rhs = compile_epformula ~use_pattern_for_enf:true ~only_pattern:true ~f:tbignonconj pf2 in
        compile_imp lhs rhs R
      end
    end
  | _ -> assert false

let rec compile_typeterm = function
  | TypeTerm.TypeConst d -> ["", d]
  | TypeVar v -> raise (Invalid_argument ("Cannot compile abstract TypeVar " ^ v))
  | TypeSum kvs -> let f (k, v) =
                     List.map (compile_typeterm v) ~f:(Util.concat k) in
                   List.concat (List.map kvs ~f)

let compile_eval_default aliases typeterm =
  compile_typeterm (
      TypeTerm.eval_default aliases (TypeTerm.TypeConst TInt) typeterm)

let compile_events pols events aliases =
  let event_list = Map.to_alist events in
  let compile_event (name, (event_type, args, _, _)) =
    let type_args (name, typ_alias) =
      let terms = compile_eval_default aliases typ_alias in
      List.map terms ~f:(Util.concat name)
    in
    let typed_args = List.concat (List.map args ~f:type_args) in
    let pol' = match Map.find pols name with
      | Some p -> enftype_to_pol p
      | None -> Lex.TObs (* TODO: is this correct?? *)
    in
    CEvent (name, event_type, pol', typed_args) (* TODO: which polarity value should be used? *)
  in
  List.map event_list ~f:compile_event

let compile_functions functions aliases =
  let function_list = Map.to_alist functions in
  let compile_function (name, (typed_args, return_type, _)) =
    let type_args (name, typ_alias) =
      let terms = compile_eval_default aliases typ_alias in
      List.map terms ~f:(Util.concat name)
    in
    let typed_args = List.concat (List.map typed_args ~f:type_args) in
    let return_type = compile_eval_default aliases return_type in
    match return_type with
    | [_, d] -> CFunction (name, typed_args, d)
    | _ -> raise (Invalid_argument ("Cannot compile function " ^ name ^ ": complex return type"))
  in
  List.map function_list ~f:compile_function


(*
let compile_exception_signature exceptions aliases variables =
  let exceptions_list = List.concat (Map.data exceptions) in
  let compile_exception_predicate (rule_name, (pred:Eformula.t)) =
    let var_types = try Map.find_exn variables rule_name with _ -> assert false in
 *)
let compile_exception_or_scope_signature pols indexed_predicates aliases variables =
  let compile_predicate (idx, pred) =
    let var_types = Map.find_exn variables idx in
    let pred_name_and_terms = match pred.f with
      | Eformula.EPredicate (n, ts, _) -> (n, ts)
      | _ -> assert false
    in
    let terms = snd pred_name_and_terms in
    let type_term f = match Eformula.ETerm.(f.trm) with
      | ETerm.TVar v ->
         let a = Map.find_exn var_types v in
         let terms = compile_eval_default aliases a in
         List.map terms ~f:(Util.concat v)
      | _ -> assert false
      (* TODO: constants are not actually possible to be part of an exception predicate *)
    in
    let typed_terms = List.concat (List.map terms ~f:type_term) in
    let pol = match Map.find pols (fst pred_name_and_terms) with
      | Some p -> enftype_to_pol p
      | None -> Lex.TObs (* TODO: is this correct? *)
      (* | None -> Lex.TItl *)
    in
    CEvent (fst pred_name_and_terms, Event (false, Standard), pol, typed_terms)
  in
  List.map indexed_predicates ~f:compile_predicate

let is_exception = function
  | ECDefinition (_, ERTException, _, _, _, _, _, _, _) -> true
  | ECDefinition (_, ERTExceptionC, _, _, _, _, _, _, _) -> true
  | _ -> false

let is_scope = function
  | ECDefinition (_, ERTScope, _, _, _, _, _, _, _) -> true
  | _ -> false

let predicate_from_definition = function
  | ECDefinition (idx, _, _, _, _, _, _, g, _) -> (idx, g)
  | _ -> assert false

let compile_signature pols events functions aliases variables let_rules =
  let event_signatures = compile_events pols events aliases in
  let function_signatures = compile_functions functions aliases in
  let exceptions = List.filter let_rules ~f:is_exception |> List.map ~f:predicate_from_definition in
  let scopes = List.filter let_rules ~f:is_scope |> List.map ~f:predicate_from_definition in
  let exception_signatures = compile_exception_or_scope_signature pols exceptions aliases variables in
  let scope_signatures = compile_exception_or_scope_signature pols scopes aliases variables in
  List.concat [event_signatures; function_signatures; exception_signatures; scope_signatures]

let is_let_rule = function
  | ECDefinition _
  | ECDefinitionDis _ -> true
  | _ -> false

let is_imp_rule = function
  | ECImplication _ -> true
  | _ -> false

let is_vanilla = function
  | ECImplication (_, _, _, _, _, _, _, Vanilla, _, _) -> true
  | _ -> false

let compile (eprog:Elex.eprog) : Clex.cprog =
  let sorted_c_rules = List.map eprog.compilation_order ~f:(Map.find_exn eprog.ecrules) in 
  let let_rules = List.filter sorted_c_rules ~f:is_let_rule in
  let imp_rules = List.filter sorted_c_rules ~f:is_imp_rule in
  let non_vanilla = List.filter imp_rules ~f:(fun r -> not (is_vanilla r)) in
  if List.is_empty non_vanilla then
    Errors.warning "No obligation rules are marked as (transparently) enforceable, compiled formula will be a tautology" None;
  debug (Printf.sprintf "Non-vanilla rules: %d" (List.length non_vanilla));
  let formulae = List.map non_vanilla ~f:compile_imp_rule in
  let let_bindings = List.map let_rules ~f:compile_let_rule in
  let phi = tbigcauconj formulae in
  let signature = compile_signature eprog.pols eprog.eevents eprog.efunctions eprog.ealiases
                    eprog.variables let_rules in
  { signature = signature;
    let_bindings = let_bindings;
    phi = phi
  }
