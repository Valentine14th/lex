open Core

open Formula.Term
open Eformula
open Lex
open Elex
open Clex

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
  | EPSince (i, g) -> let neg_f = { f = ENeg f; enftype = Non; id = 0} in
                      let since_f = { f = ESince (R, i, neg_f, g); enftype = Non; id = 0 } in
                      { f = ENeg since_f; enftype = Non; id = 0 }

let complete_erule (eprog:Elex.eprog) =
  let aux f' = function
    | EObligation (f, p, g, q) -> EObligation (f@f', p, g, q)
    | EPermission (f, p, g, q) -> EPermission (f@f', p, g, q)
    | EConstitutive (f, p, g) -> EConstitutive (f@f', p, g)
    | EException (f, p, ref, pred) -> EException (f@f', p, ref, pred)
    | EExceptionC (f, p, ref, pred, g) -> EExceptionC (f@f', p, ref, pred, g)
    | EScope (f, p, ref, pred) -> EScope (f@f', p, ref, pred)
  in
  function
  | ESRule (_, idx, _, _, rule, _, _, _) ->
    let exception_idxs' = Map.find_multi eprog.rule_tree.exceptions idx in
    let scope_idxs' = Map.find_multi eprog.rule_tree.scopes idx in
    let exception_idxs = List.filter exception_idxs' ~f:(fun x -> x=idx) in
    let scope_idxs = List.filter scope_idxs' ~f:(fun x -> x=idx) in
    let exception_predicates = List.map exception_idxs ~f:(try Map.find_exn eprog.exception_predicates with _ -> assert false) in
    let exception_predicates_neg = List.map exception_predicates ~f:(fun x -> make (eneg x) Non 0) in
    let exception_positions = List.map exception_idxs ~f:(fun x -> try snd (Map.find_exn eprog.rule_tree.label_of_rule x) with _ -> assert false) in
    let exceptions = List.zip_exn exception_positions exception_predicates_neg in
    let scope_predicates = List.map scope_idxs ~f:(try Map.find_exn eprog.scope_predicates with _ -> assert false) in
    let scope_positions = List.map scope_idxs ~f:(fun x -> try snd (Map.find_exn eprog.rule_tree.label_of_rule x) with _ -> assert false) in
    let scopes = List.zip_exn scope_positions scope_predicates in
    let rule' = aux (exceptions@scopes) rule in
    rule'
  | _ -> assert false

let compile_let_binding f p pred =
  let lhs = pred in
  let rhs = (compile_pattern (tbigcauconj f) p) in
  (lhs, rhs)

let compile_erule_let = function
  | EObligation _ | EPermission _ -> None
  | EConstitutive (f, p, pred) ->
    let binding = begin match pred with
      | [(_, { f = EPredicate _; _})] -> compile_let_binding (List.map ~f:snd f) p (List.hd_exn pred |> snd)
      | _ -> assert false
    end in
    Some binding
  | EException (f, p, _, pred) -> Some (compile_let_binding (List.map ~f:snd f) p pred)
  | EScope (f, p, _, pred) -> Some (compile_let_binding (List.map ~f:snd f) p pred)
  | EExceptionC _ -> assert false

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

let compile_erule_imp = function
  | EObligation (f, p, g, q) -> Some (compile_imp (List.map ~f:snd f) p (List.map ~f:snd g) q)
  | EPermission (f, p, g, q) -> Some (compile_imp (List.map ~f:snd f) p (List.map ~f:snd g) q)
  | EConstitutive _ | EException _ | EExceptionC _ | EScope _ -> None

let rec compile_typeterm = function
  | Formula.TypeTerm.TypeConst d -> ["", d]
  | TypeVar v -> raise (Invalid_argument ("Cannot compile abstract TypeVar " ^ v))
  | TypeSum kvs -> let f (k, v) =
                     List.map (compile_typeterm v) ~f:(Etc.concat k) in
                   List.concat (List.map kvs ~f)

let compile_eval_default aliases typeterm =
  compile_typeterm (
      Formula.TypeTerm.eval_default aliases (Formula.TypeTerm.TypeConst TInt) typeterm)

let compile_events events aliases =
  let event_list = Map.to_alist events in
  let compile_event (name, (event_type, args, pol, _)) =
    let type_args (_, name, typ_alias) =
      let terms = compile_eval_default aliases typ_alias in
      List.map terms ~f:(Etc.concat name)
    in
    let typed_args = List.concat (List.map args ~f:type_args) in
    CEvent (name, event_type, pol, typed_args)
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

(* TODO: constants inside of predicates do not
   actually introduce an unnamed variable for the
   "exception" predicate...
   i.e. being able to create a fresh name for variables
   is not needed*)
let c = ref 0
let fresh_var () = incr c; "_v" ^ string_of_int !c

(*
let compile_exception_signature exceptions aliases variables =
  let exceptions_list = List.concat (Map.data exceptions) in
  let compile_exception_predicate (rule_name, (pred:Eformula.t)) =
    let var_types = try Map.find_exn variables rule_name with _ -> assert false in
 *)
let compile_exception_or_scope_signature predicate_map aliases variables =
  let indexed_predicates = (Map.to_alist predicate_map) in
  let compile_predicate (idx, pred) =
    let var_types = try Map.find_exn variables idx with _ -> assert false in
    let pred_name_and_terms = match pred.f with
      | Eformula.EPredicate (n, ts, _) -> (n, ts)
      | _ -> assert false
    in
    let terms = snd pred_name_and_terms in
    let type_term f = match Eformula.Term.(f.trm) with
      | Term.TVar v ->
         let a = try Map.find_exn var_types v with _ -> assert false in
      (* TODO: check how this should behave *)
      (* | Term.TVar v -> let a = try Map.find_exn var_types v with _ -> Formula.TypeTerm.TypeConst TInt in *)
         let terms = compile_eval_default aliases a in
         List.map terms ~f:(Etc.concat v)
      | _ -> assert false
      (* TODO: constants are not actually possible to be part of an exception predicate *)
    in
    let typed_terms = List.concat (List.map terms ~f:type_term) in
    CEvent (fst pred_name_and_terms, Event (false, Standard), Lex.TInternal, typed_terms)
  in
  List.map indexed_predicates ~f:compile_predicate

let compile_signature events functions aliases variables exceptions scopes =
  let event_signatures = compile_events events aliases in
  let function_signatures = compile_functions functions aliases in
  let exception_signatures = compile_exception_or_scope_signature exceptions aliases variables in
  let scope_signatures = compile_exception_or_scope_signature scopes aliases variables in
  List.concat [event_signatures; function_signatures; exception_signatures; scope_signatures]


(* TODO (JD): implement topological sorting for let bindings *)
let topological_sort_erules rules = rules


let rec remove_special = function
  | [] -> []
  | EExceptionC (f, p, refs, pred, g) :: t ->
     EException (f, p, refs, pred) :: EConstitutive (f, p, g) :: (remove_special t)
  | h :: t -> h :: (remove_special t)

let compile (eprog:Elex.eprog) =
  let rules' = List.filter eprog.estmts ~f:is_erule in
  let rules = remove_special (List.map rules' ~f:(complete_erule eprog)) in
  let sorted_rules = topological_sort_erules rules in
  let let_bindings = List.filter_map sorted_rules ~f:compile_erule_let in
  let formulae = List.filter_map sorted_rules ~f:compile_erule_imp in
  let phi = tbigcauconj formulae in
  let signature = compile_signature eprog.eevents eprog.efunctions eprog.ealiases
                    eprog.variables eprog.exception_predicates eprog.scope_predicates in
  { signature; let_bindings; phi }
