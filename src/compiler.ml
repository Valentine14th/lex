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
  
let compile tprog =
  let rules = List.filter tprog.tstmts ~f:is_trule in
  let formulae = List.map rules ~f:(compile_trule tprog) in
  let phi = bigconj formulae in
  Printf.printf "%s\n" (Formula.to_string phi)
