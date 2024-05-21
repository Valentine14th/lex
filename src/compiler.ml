open Core

open Formula.Term
open Eformula
open Lex
open Elex

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
       let f = compile_unop (compile_tt (Formula.TypeTerm.eval aliases term.tt)) op in
       Term.TApp (f, [compile_term aliases term])
    | Term.TBinop (term, op, term') ->
       let f = compile_binop
                 (compile_tt (Formula.TypeTerm.eval aliases term.tt))
                 (compile_tt (Formula.TypeTerm.eval aliases term'.tt)) op in
       Term.TApp (f, [compile_term aliases term; compile_term aliases term'])
  in { term with trm }

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

let compile_erule eprog =
  let aux f' = function
    | EObligation (f, p, g, q) -> compile_imp (List.map ~f:snd f@f') p (List.map ~f:snd g) q
    | EPermission (f, p, g, q) -> compile_imp (List.map ~f:snd f@f') p (List.map ~f:snd g) q
    | EConstitutive (f, p, g) -> compile_imp (List.map ~f:snd f@f') p (List.map ~f:snd g) EPPresent
    | EException (f, p, _, pred) -> compile_imp (List.map ~f:snd f@f') p [pred] EPPresent (* TODO: implement exception compilation to more closely represent let expressions, maybe with iff instead of just if *)
    | EScope (f, p, _, pred) -> compile_imp (List.map ~f:snd f@f') p [pred] EPPresent (* TODO is a negation necessary here, or is this handled elsewhwere? *)
  in
  function
(*
  | ESRule (_, label, _, rule, _, _, _) ->
    let label_name = Label.qualified_name label in
    let exceptions = Map.find_multi eprog.exceptions label_name in
    let f' = List.map exceptions ~f:(fun x -> make (eneg (snd x)) Non 0) in
    aux f' rule
 *)
  | ESRule (_, idx, _, _, rule, _, _, _) ->
    let exception_idxs = Map.find_multi eprog.rule_tree.exceptions idx in
    let scope_idxs = Map.find_multi eprog.rule_tree.scopes idx in
    let exceptions = List.map exception_idxs ~f:(try Map.find_exn eprog.exception_predicates with _ -> assert false) in
    let scopes = List.map scope_idxs ~f:(try Map.find_exn eprog.scope_predicates with _ -> assert false) in
    let f' = List.map exceptions ~f:(fun x -> make (eneg x) Non 0) in
    aux (f'@scopes) rule
  | _ -> assert false

type signature_item =
  | CEvent of ident * event_type * pol * ((ident * Dom.tt) list)
  | CFunction of ident * ((ident * Dom.tt) list) * Dom.tt

let compile_events events aliases =
  let event_list = Map.to_alist events in
  let compile_event (name, (event_type, args, pol, _)) =
    let type_args (_, name, typ_alias) =
      (name, Formula.TypeTerm.eval aliases typ_alias)
    in
    let typed_args = List.map args ~f:type_args in
    CEvent (name, event_type, pol, typed_args)
  in
  List.map event_list ~f:compile_event

let compile_functions functions aliases =
  let function_list = Map.to_alist functions in
  let compile_function (name, (typed_args, return_type, _)) =
    let type_args (name, typ_alias) =
      (name, Formula.TypeTerm.eval aliases typ_alias)
    in
    let typed_args = List.map typed_args ~f:type_args in
    let return_type = Formula.TypeTerm.eval aliases return_type in
    CFunction (name, typed_args, return_type)
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
      | Eformula.EPredicate (n, ts) -> (n, ts)
      | _ -> assert false
    in
    let terms = snd pred_name_and_terms in
    let type_term f = match Eformula.Term.(f.trm) with
      | Term.TVar v -> let a = try Map.find_exn var_types v with _ -> assert false in
                       let t = Formula.TypeTerm.eval aliases a in
                       (v, t)
      | _ -> assert false
      (* TODO: constants are not actually possible to be part of an exception predicate *)
    in
    let typed_terms = List.map terms ~f:type_term in
    CEvent (fst pred_name_and_terms, Event false, Lex.TInternal, typed_terms)
  in
  List.map indexed_predicates ~f:compile_predicate

let compile_signature events functions aliases variables exceptions scopes =
  let event_signatures = compile_events events aliases in
  let function_signatures = compile_functions functions aliases in
  let exception_signatures = compile_exception_or_scope_signature exceptions aliases variables in
  let scope_signatures = compile_exception_or_scope_signature scopes aliases variables in
  List.concat [event_signatures; function_signatures; exception_signatures; scope_signatures]

let pol_to_symbol_string pol =
  match pol with
  | TCau -> "+"
  | TSup -> "-"
  | TCauSup -> "+-"
  | TInternal -> "+-" (* TODO: are internal events acutally both causable and suppressable? and are exception predicates of internal type? *)
  | TObs -> ""

let string_of_signatures signatures =
  let string_of_event_type = function
    | Event true  -> "ext "
    | Event false -> ""
    | Predicate   -> "pred" in
  let string_of_event_signature (name, event_type, pol, args) =
    let arg_strs = List.map args ~f:(fun (name, tt) ->
      Printf.sprintf "%s: %s" name (Dom.string_of_tt tt)) in
    let args_str = String.concat ~sep:", " arg_strs in
    Printf.sprintf "%s%s(%s)%s" name (string_of_event_type event_type) args_str (pol_to_symbol_string pol)
  in
  let string_of_function_signature (name, args, ret_tt) =
    let arg_strs = List.map args ~f:(fun (name, tt) ->
      Printf.sprintf "%s: %s" name (Dom.string_of_tt tt)) in
    let args_str = String.concat ~sep:", " arg_strs in
    Printf.sprintf "fun %s(%s) -> %s" name args_str (Dom.string_of_tt ret_tt)
  in
  let string_of_signature_item = function
    | CEvent (name, event_type, pol, args) ->
       string_of_event_signature (name, event_type, pol, args)
    | CFunction (name, args, ret_tt) ->
       string_of_function_signature (name, args, ret_tt) in
  let signature_strs = List.map signatures ~f:string_of_signature_item in
  String.concat ~sep:"\n" signature_strs

let compile (eprog:Elex.eprog) =
  let rules = List.filter eprog.estmts ~f:is_erule in
  let formulae = List.map rules ~f:(compile_erule eprog) in
  let phi = tbigcauconj formulae in
  let signatures = compile_signature eprog.eevents eprog.efunctions eprog.ealiases
                     eprog.variables eprog.exception_predicates eprog.scope_predicates in
  Printf.printf "Signature:\n%s\n\nFormula:\n%s\n"
    (string_of_signatures signatures)
    (Eformula.to_string phi)
