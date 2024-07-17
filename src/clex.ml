open Core

open Lex

type signature_item =
  | CEvent of ident * event_type * pol * ((ident * Dom.tt) list)
  | CFunction of ident * ((ident * Dom.tt) list) * Dom.tt

type let_binding = Eformula.t * Eformula.t

type cprog =
  {
    signature:    signature_item list;
    let_bindings: let_binding list;
    phi:          Eformula.t
  }

let pol_to_symbol_string pol =
  match pol with
  | TCau -> "+"
  | TCauObs -> "+"
  | TSup -> "-"
  | TCauSup -> "+-"
  | TItl -> "+-" (* TODO: are internal events acutally both causable and suppressable? and are exception predicates of internal type? *)
  | TObs -> ""

let string_of_signatures signatures =
  let string_of_event_type = function
    | Event (true, _)  -> "ext "
    | Event (false, _) -> ""
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

let string_of_let_binding (lhs, rhs) =
  let lhs_str = Formula.to_string (Eformula.to_formula lhs) in
  let rhs_str = Formula.to_string (Eformula.to_formula rhs) in
  Printf.sprintf "let %s = %s" lhs_str rhs_str

let to_string cprog =
  Printf.sprintf "Signature:\n%s\n\nFormula:\n%s\n%s\n"
    (string_of_signatures cprog.signature)
    ((List.map cprog.let_bindings ~f:string_of_let_binding) |> String.concat ~sep:"\n")
    (Formula.to_string (Eformula.to_formula cprog.phi))
