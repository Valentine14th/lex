open Core

open Lex

type signature_item = 
  | CEvent of ident * event_type * Enftype.t * ((ident * Dom.tt) list)
  | CFunction of ident * ((ident * Dom.tt) list) * Dom.tt

type let_binding = Eformula.t * Eformula.t

type cprog =
  {
    signature:    signature_item list;
    let_bindings: let_binding list;
    phi:          Eformula.t
  }

let pol_to_symbol_string enftype =
  if Enftype.is_causable enftype then (
    if Enftype.is_suppressable enftype then
      "+-"
    else if Enftype.is_observable enftype then
      "+"
    else
      "+?"
  )
  else if Enftype.is_suppressable enftype then
    "-"
  else if Enftype.is_observable enftype then
    ""
  else
    "?"

let string_of_signatures signatures =
  let string_of_event_type = function
    | Event (true, _)  -> "ext "
    | Event (false, _) -> ""
    | Predicate   -> "pred " in
  let string_of_event_signature (name, event_type, pol, args) =
    let arg_strs = List.map args ~f:(fun (name, tt) ->
      Printf.sprintf "%s: %s" name (Dom.tt_to_string tt)) in
    let args_str = String.concat ~sep:", " arg_strs in
    Printf.sprintf "%s%s(%s)%s" (string_of_event_type event_type)
      name args_str (pol_to_symbol_string pol)
  in
  let string_of_function_signature (name, args, ret_tt) =
    let arg_strs = List.map args ~f:(fun (name, tt) ->
      Printf.sprintf "%s: %s" name (Dom.tt_to_string tt)) in
    let args_str = String.concat ~sep:", " arg_strs in
    Printf.sprintf "fun %s(%s) -> %s" name args_str (Dom.tt_to_string ret_tt)
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
  (* let lhs_str = (Eformula.to_string lhs) in
  let rhs_str = (Eformula.to_string rhs) in *)
  Printf.sprintf "LET %s = %s IN" lhs_str rhs_str

let to_string cprog =
  Printf.sprintf "Signature:\n%s\n\nFormula:\n%s\n%s\n"
    (string_of_signatures cprog.signature)
    (List.map cprog.let_bindings ~f:string_of_let_binding
     |> String.concat ~sep:"\n")
    (* (Eformula.to_string cprog.phi) *)
    (Formula.to_string (Eformula.to_formula cprog.phi))

let to_files cprog sig_fn formula_fn =
  Out_channel.with_file sig_fn ~f:(fun oc ->
      Out_channel.output_string oc
        (string_of_signatures cprog.signature));
  Out_channel.with_file formula_fn ~f:(fun oc ->
      Out_channel.output_string oc
        (List.map cprog.let_bindings ~f:(fun lb -> string_of_let_binding lb ^ "\n") |> String.concat);
      Out_channel.output_string oc
        (Formula.to_string (Eformula.to_formula cprog.phi)))
