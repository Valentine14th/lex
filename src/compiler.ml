open Core

open Formula
open Lex
open Tlex

let compile_imp f g =
  let vars =
    Set.elements
      (Set.union_list (module String)
         (List.map f ~f:fv @ List.map g ~f:fv)) in
  Always
    (Interval.full,
     bigforall vars (Imp (N, bigconj f, bigconj g)))

let compile_trule tprog =
  let aux f' = function
    | TObligation (f, g) -> compile_imp (f@f') g
    | TPermission (f, g) -> compile_imp (f@f') g
    | TConstitutive (f, g) -> compile_imp (f@f') g
    | TException (f, _, pred) -> compile_imp (f@f') [pred]
  in
  function
  | TSRule (_, label, rule, _, _, _) ->
    let label_name = Label.qualified_name label in
    let exceptions = Map.find_multi tprog.exceptions label_name in
    let f' = List.map exceptions ~f:(fun x -> neg (snd x)) in
    aux f' rule
  | _ -> assert false

let compile_events events aliases =
  let event_list = Map.to_alist events in
  let compile_event (name, (args, pol, _)) =
    let type_args (_, name, typ_alias) =
      let typ = Map.find_exn aliases typ_alias in
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
    let pred_name_and_terms = match pred with
      | Formula.Predicate (n, ts) -> (n, ts)
      | _ -> assert false
    in
    let terms = snd pred_name_and_terms in
    let type_term = function
      | Term.Var v -> let a = try Map.find_exn var_types v with _ -> assert false in
                      let t = try Map.find_exn aliases a with _ -> assert false in
                      (v, t)
      (* TODO: constants are not actually possible to be part of an exception predicate *)
      | Term.Const (Int _) -> (fresh_var (), TInt)
      | Term.Const (Str _) -> (fresh_var (), TString)
      | Term.Const (Float _) -> assert false (* TODO: floats not supported yet *)
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

let compile tprog =
  let rules = List.filter tprog.tstmts ~f:is_trule in
  let formulae = List.map rules ~f:(compile_trule tprog) in
  let phi = bigconj formulae in
  let signatures = compile_signature tprog.tevents tprog.taliases tprog.variables tprog.exceptions in
  Printf.printf "Signature:\n%s\n\nFormula:\n%s\n"
    (string_of_signatures signatures)
    (Formula.to_string phi)
