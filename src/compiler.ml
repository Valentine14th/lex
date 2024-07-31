open Core

open Formula.Term
open Eformula
open Lex
open Elex
open Clex

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

let compile_pattern (f: Eformula.t) = function
  | EPPresent -> f
  | EPEventually i -> { f = EEventually (i, Interval.is_bounded i, f); enftype = Non; id = 0 }
  | EPAlways i -> { f = EAlways (i, Interval.is_bounded i, f); enftype = Non; id = 0 }
  | EPUntil (i, g) -> { f = EUntil (R, i, Interval.is_bounded i, g, f); enftype = Non; id = 0 }
  | EPOnce i -> { f = EOnce (i, f); enftype = Non; id = 0 }
  | EPHistorically i -> { f = EHistorically (i, f); enftype = Non; id = 0 }
  | EPSince (i, g) -> { f = ESince (R, i, f, g); enftype = Non; id = 0 }

let compile_let_binding f p pred : Eformula.t * Eformula.t =
  match pred with
  | { f = EPredicate (p_name, trms, event_type); _} ->
     let process_term f (trm: Tformula.Term.t) =
       match trm.trm with
       | Term.TVar _ -> f, trm
       | _ -> let v = Term.{ trm = Term.TVar (fresh_var ()); tt = trm.tt } in
              let eq = Term.{ trm = Term.TBinop (v, Formula.Term.BEq, trm);
                              tt = Formula.TypeTerm.TypeConst Dom.TBool } in
              { f = EEqConst (eq, Dom.Bool true); enftype = Formula.EnfType.Obs; id = 0} :: f, v in
     let f', trms = List.fold_map trms ~init:[] ~f:process_term in
     let f = f @ List.rev f' in
     let lhs = { pred with f = EPredicate (p_name, trms, event_type) } in
     let rhs = (compile_pattern (tbigcauconj f) p) in
     (lhs, rhs)
  | _ -> assert false

let compile_let_rule = function
  | ECDefinition (_, _, _, f, e, s, p, _, g) ->
    let f = List.map f ~f:snd in
    let e = List.map e ~f:snd in
    let e_neg = List.map e ~f:(fun x -> make (ENeg x) Non 0) in
    let s = List.map s ~f:snd in
    compile_let_binding (f @ e_neg @ s) p g
  | ECDefinitionDis _ -> assert false (* TODO *)
  | _ -> assert false

let compile_imp f p g q =
  let vars =
    Set.elements
      (Set.union_list (module String)
         (List.map f ~f:fv @ List.map g ~f:fv)) in
  make (EAlways
    (Interval.full,
     true,
     tbigcauforall vars
       ((make (EImp (N, compile_pattern
                          (tbigcauconj f) p, compile_pattern (tbigcauconj g) q)) Non 0))))
    Non 0

let compile_imp_rule = function
  | ECImplication (_, _, _, f, e, s, p, g, q, _, _) ->
    let f = List.map f ~f:snd in
    let e = List.map e ~f:snd in
    let s = List.map s ~f:snd in
    let g = List.map g ~f:snd in
    let e_neg = List.map e ~f:(fun x -> make (ENeg x) Non 0) in
    compile_imp (f @ e_neg @ s) p g q
  | _ -> assert false

let rec compile_typeterm = function
  | Formula.TypeTerm.TypeConst d -> ["", d]
  | TypeVar v -> raise (Invalid_argument ("Cannot compile abstract TypeVar " ^ v))
  | TypeSum kvs -> let f (k, v) =
                     List.map (compile_typeterm v) ~f:(Etc.concat k) in
                   List.concat (List.map kvs ~f)

let compile_eval_default aliases typeterm =
  compile_typeterm (
      Formula.TypeTerm.eval_default aliases (Formula.TypeTerm.TypeConst TInt) typeterm)

let compile_events pols events aliases =
  let event_list = Map.to_alist events in
  (* let compile_event (name, (event_type, args, pol, _)) = *)
  let compile_event (name, (event_type, args, _, _)) =
    let type_args (_, name, typ_alias) =
      let terms = compile_eval_default aliases typ_alias in
      List.map terms ~f:(Etc.concat name)
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
      List.map terms ~f:(Etc.concat name)
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
    let type_term f = match Eformula.Term.(f.trm) with
      | Term.TVar v ->
         let a = Map.find_exn var_types v in
         let terms = compile_eval_default aliases a in
         List.map terms ~f:(Etc.concat v)
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
  | ECDefinition (idx, _, _, _, _, _, _, _, g) -> (idx, g)
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

let compile (eprog:Elex.eprog) : Clex.cprog =
  let sorted_c_rules = List.map eprog.compilation_order ~f:(Map.find_exn eprog.compilation_rules) in 
  let let_rules = List.filter sorted_c_rules ~f:is_let_rule in
  let imp_rules = List.filter sorted_c_rules ~f:is_imp_rule in
  let formulae = List.map imp_rules ~f:compile_imp_rule in
  let let_bindings = List.map let_rules ~f:compile_let_rule in
  let phi = tbigcauconj formulae in
  let signature = compile_signature eprog.pols eprog.eevents eprog.efunctions eprog.ealiases
                    eprog.variables let_rules in
  { signature = signature;
    let_bindings = let_bindings;
    phi = phi }
