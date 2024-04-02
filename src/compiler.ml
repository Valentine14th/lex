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
    | Obligation (f, g) -> compile_imp (f@f') g
    | Permission (f, g) -> compile_imp (f@f') g
    | Constitutive (f, g) -> compile_imp (f@f') g
    | _ -> assert false
  in
  function
  | TSRule (labels, rule, _, _) ->
     let exceptions = List.concat (List.map labels ~f:(Map.find_multi tprog.exceptions)) in
     let f' = List.map exceptions ~f:neg in
     aux f' rule
  | _ -> assert false

(* TODO: should redefining event names be allowed?
   if yes, some event name prefixing is needed
   to ensure events have unique names in the produced
   signature *)
let compile_events events aliases =
  let event_list = Map.fold events ~f:(fun ~key:key ~data:value acc -> (key, value) :: acc) ~init:[] in
  let compile_event (name, (args, pol, _)) =
    let type_args (name, typ_alias) =
      let typ = Map.find_exn aliases typ_alias in
      (name, typ)
    in
    let typed_args = List.map args ~f:type_args in
    (name, pol, typed_args)
  in
  List.map event_list ~f:compile_event

let pol_to_symbol_string pol =
  match pol with
  | TCau -> "+"
  | TSup -> "-"
  | TCauSup -> "+-"
  | TInternal -> "+-" (* TODO: is this correct? *)
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
  let signatures = compile_events tprog.tevents tprog.taliases in
  Printf.printf "Signature:\n%s\n\nFormula:\n%s\n"
    (string_of_signatures signatures)
    (Formula.to_string phi)
