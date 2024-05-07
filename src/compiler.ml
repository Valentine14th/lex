open Core

open Formula
open Tformula
open Lex
open Elex

let compile_imp f g =
  let vars =
    Set.elements
      (Set.union_list (module String)
         (List.map f ~f:fv @ List.map g ~f:fv)) in
  make (TAlways
    (Interval.full,
     true,
     tbigcauforall vars ((make (TImp (N, tbigcauconj f, tbigcauconj g)) Non 0))))
    Non 0

let compile_erule eprog =
  let aux f' = function
    | EObligation (f, g) -> compile_imp (f@f') g
    | EPermission (f, g) -> compile_imp (f@f') g
    | EConstitutive (f, g) -> compile_imp (f@f') g
    | EException (f, _, pred) -> compile_imp (f@f') [pred]
  in
  function
  | ESRule (_, label, _, rule, _, _, _) ->
    let label_name = Label.qualified_name label in
    let exceptions = Map.find_multi eprog.exceptions label_name in
    let f' = List.map exceptions ~f:(fun x -> make (tneg (snd x)) Non 0) in
    aux f' rule
  | _ -> assert false

let compile_events events aliases =
  let event_list = Map.to_alist events in
  let compile_event (name, (args, pol, _)) =
    let type_args (_, name, typ_alias) =
      let typ = fst (Map.find_exn aliases typ_alias) in
      (name, typ)
    in
    let typed_args = List.map args ~f:type_args in
    (name, pol, typed_args)
  in
  List.map event_list ~f:compile_event

(* TODO: constants inside of predicates do not
   actually introduce an unnamed variable for the
   "exception" predicate...
   i.e. being able to create a fresh name for variables
   is not needed*)
let c = ref 0
let fresh_var () = incr c; "_v" ^ string_of_int !c

let compile_exception_signature exceptions aliases variables =
  let exceptions_list = List.concat (Map.data exceptions) in
  let compile_exception_predicate (rule_name, pred) =
    let var_types = try Map.find_exn variables rule_name with _ -> assert false in
    let pred_name_and_terms = match pred.f with
      | Tformula.TPredicate (n, ts) -> (n, ts)
      | _ -> assert false
    in
    let terms = snd pred_name_and_terms in
    let type_term = function
      | Term.Var v -> let a = try Map.find_exn var_types v with _ -> assert false in
                      let t = try Map.find_exn aliases a with _ -> assert false in
                      (v, fst t)
      (* TODO: constants are not actually possible to be part of an exception predicate *)
      | Term.Const (Int _) -> (fresh_var (), TInt)
      | Term.Const (Str _) -> (fresh_var (), TString)
      | Term.Const (Float _) -> (fresh_var (), TFloat)
    in
    let typed_terms = List.map terms ~f:type_term in
    (fst pred_name_and_terms, Lex.TInternal, typed_terms)
  in
  List.map exceptions_list ~f:compile_exception_predicate


let compile_signature events aliases variables exceptions =
  let event_signatures = compile_events events aliases in
  let exception_signatures = compile_exception_signature exceptions aliases variables in
  List.concat [event_signatures; exception_signatures]

let pol_to_symbol_string pol =
  match pol with
  | TCau -> "+"
  | TSup -> "-"
  | TCauSup -> "+-"
  | TInternal -> "+-" (* TODO: are internal events acutally both causable and suppressable? and are exception predicates of internal type? *)
  | TObs -> ""

let string_of_signatures signatures =
  let string_of_signature (name, pol, args) =
    let arg_strs = List.map args ~f:(fun (name, typ) ->
      Printf.sprintf "%s: %s" name (string_of_typ typ)) in
    let args_str = String.concat ~sep:", " arg_strs in
    Printf.sprintf "%s(%s)%s" name args_str (pol_to_symbol_string pol)
  in
  let signature_strs = List.map signatures ~f:string_of_signature in
  String.concat ~sep:"\n" signature_strs

let compile eprog =
  let rules = List.filter eprog.estmts ~f:is_erule in
  let formulae = List.map rules ~f:(compile_erule eprog) in
  let phi = tbigcauconj formulae in
  let signatures = compile_signature eprog.eevents eprog.ealiases eprog.variables eprog.exceptions in
  Printf.printf "Signature:\n%s\n\nFormula:\n%s\n"
    (string_of_signatures signatures)
    (Tformula.to_string phi)
