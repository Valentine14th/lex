open Core
open Elex
open Html

module Placeholders = struct
  
  let regex =
    Re.compile (Re.(seq [char '{'; group (rep alpha); char '}']))

  let replace_all names trms s =
    let names_trms = List.zip_exn names trms in
    let f group =
      List.Assoc.find_exn names_trms ~equal:String.equal (Re.Group.get group 1) in
    Re.replace regex ~f s

  let mark_all s =
    let f group = span "lex-formula-term" (Re.Group.get group 1) in
    Re.replace regex ~f s

end

let reading_of_term term =
  span "lex-formula-term" (Formula.Term.value_to_string term)

let reading_of_past_interval default = function
  | Interval.U (UI 0) -> default  ^ " in the past"
  | U (UI i) -> Printf.sprintf "%s at least %d time units ago" default i
  | B (BI (0, j)) -> Printf.sprintf "%s within %d time units" default j
  | B (BI (i, j)) -> Printf.sprintf "%s between %d and %d time units ago" default i j

let reading_of_future_interval default = function
  | Interval.U (UI 0) -> default ^ " in the future"
  | U (UI i) -> Printf.sprintf "%s in at least %d time units" default i
  | B (BI (0, j)) -> Printf.sprintf "%s within %d time units" default j
  | B (BI (i, j)) -> Printf.sprintf "%s in between %d and %d time units" default i j
    
let rec reading_of_formula formula_id eprog f =
  let inner_html = 
    match Tformula.(f.f) with
    | Tformula.TTT -> const "true"
    | TFF -> const "false"
    | TEqConst (x, d) -> ident x ^ " is equal to " ^ const (Dom.to_string d)
    | TPredicate (name, trms) as f ->
       (match Map.find Elex.(eprog.eevents) name with
        | Some (args, _, doc_string) -> 
           let names = List.map ~f:(fun (_, name, _) -> name) args in
           (match doc_string with
            | None   -> Tformula.to_string_core f
            | Some s -> Placeholders.replace_all names (List.map ~f:reading_of_term trms) s)
        | None -> Tformula.to_string_core f)
    | TNeg f ->
       "the following is not the case: "
       ^ (ul "lex-reading-neg"
            (li "lex-reading-neg-li" (reading_of_formula formula_id eprog f)))
    | TAnd (_, f, g) ->
       "all of the following are the case:"
       ^ (ul "lex-reading-and"
            ((li "lex-reading-and-li" (reading_of_formula formula_id eprog f))
             ^ (li "lex-reading-and-li" (reading_of_formula formula_id eprog g))))
    | TOr (_, f, g) ->
       "at least one of the following is the case:"
       ^ (ul "lex-reading-or"
            ((li "lex-reading-or-li" (reading_of_formula formula_id eprog f))
             ^ (li "lex-reading-or-li" (reading_of_formula formula_id eprog g))))
    | TImp (_, f, g) ->
       "if the following is the case:"
       ^ (ul "lex-reading-imp-left"
            (li "lex-reading-imp-left-li" (reading_of_formula formula_id eprog f)))
       ^ "then the following is the case:"
       ^ (ul "lex-reading-imp-right"
            (li "lex-reading-imp-right-li" (reading_of_formula formula_id eprog g)))
    | TIff (_, _, f, g) ->
       "the following is the case:"
       ^ (ul "lex-reading-iff-left"
            (li "lex-reading-iff-left-li" (reading_of_formula formula_id eprog f)))
       ^ "if, and only if, the following is the case:"
       ^ (ul "lex-reading-iff-right"
            (li "lex-reading-iff-right-li" (reading_of_formula formula_id eprog g)))
    | TExists (x, f) ->
       "there exists " ^ ident x ^ " such that the following is the case:"
       ^ (ul "lex-reading-exists"
            (li "lex-reading-exists-li" (reading_of_formula formula_id eprog f)))
    | TForall (x, f) ->
       "for all " ^ ident x ^ ", the following is the case:"
       ^ (ul "lex-reading-forall"
            (li "lex-reading-forall-li" (reading_of_formula formula_id eprog f)))
    | TPrev (i, f) ->
       reading_of_past_interval "at the previous time point" i
       ^ ", the following happened:"
       ^ (ul "lex-reading-prev"
            (li "lex-reading-prev-li" (reading_of_formula formula_id eprog f)))
    | TNext (i, f) ->
       reading_of_future_interval "at the next time point" i
       ^ ", the following will happen:"
       ^ (ul "lex-reading-next"
            (li "lex-reading-next-li" (reading_of_formula formula_id eprog f)))
    | TOnce (i, f) ->
       reading_of_past_interval "at some point" i
       ^ ", the following happened: "
       ^ (ul "lex-reading-once"
            (li "lex-reading-once-li" (reading_of_formula formula_id eprog f)))
    | TEventually (i, _, f) ->
       reading_of_future_interval "at some point" i
       ^ ", the following will happen: "
       ^ (ul "lex-reading-eventually"
            (li "lex-reading-eventually-li" (reading_of_formula formula_id eprog f)))
    | THistorically (i, f) ->
       reading_of_past_interval "at all time points" i
       ^ ", the following happened: "
       ^ (ul "lex-reading-historically"
            (li "lex-reading-historically-li" (reading_of_formula formula_id eprog f)))
    | TAlways (i, _, f) ->
       reading_of_future_interval "at all time points" i
       ^ ", the following happened: "
       ^ (ul "lex-reading-always"
            (li "lex-reading-always-li" (reading_of_formula formula_id eprog f)))
    | TSince (_, i, f, g) ->
       reading_of_past_interval "at some point" i
       ^ ", the following happened: "
       ^ (ul "lex-reading-since-left"
            (li "lex-reading-since-left-li" (reading_of_formula formula_id eprog f)))
       ^ "and since then the following has always been the case:"
       ^ ", the following happened: "
       ^ (ul "lex-reading-since-right"
            (li "lex-reading-since-right-li" (reading_of_formula formula_id eprog g)))
    | TUntil (_, i, _, f, g) ->
       reading_of_future_interval "at some point" i
       ^ ", the following will happen: "
       ^ (ul "lex-reading-until-left"
            (li "lex-reading-until-left-li" (reading_of_formula formula_id eprog f)))
       ^ "and until then the following will always be the case:"
       ^ ", the following happened: "
       ^ (ul "lex-reading-until-right"
            (li "lex-reading-until-right-li" (reading_of_formula formula_id eprog g)))
    | f -> Tformula.to_string_core f in
  let id = Some (Printf.sprintf "%s-%d" formula_id f.id) in
  div ~id "lex-subformula-reading" inner_html 

let reading_of_rule_if prefix_id eprog g =
  let formula_id = Printf.sprintf "%s-%d" prefix_id in
  let f i g =
    li "lex-reading-if-formula" (reading_of_formula (formula_id i) eprog g) in
  p "lex-reading-if" (
      "Whenever all of the following happen:"
      ^ ul "lex-reading-if-formulae"
          (String.concat ~sep:"" (List.mapi ~f g))
    )

let reading_of_rule_then prefix_id eprog verb g =
  let formula_id = Printf.sprintf "%s-%d" prefix_id in
  let f i g =
    li "lex-reading-then-formula" (reading_of_formula (formula_id i) eprog g) in
  p "lex-reading-then" (
      "Then the following "
      ^ strong "lex-reading-verb" verb
      ^ ":"
      ^ ul "lex-reading-then-formulae"
          (String.concat ~sep:"" (List.mapi ~f g))
    )

let reading_of_rule_except ident =
  p "lex-reading-then" (
      "rule " ^ ident ^ " does not apply"
    )

let verb_of_erule = function
  | EObligation _ -> "must happen"
  | EPermission _ -> "is permitted"
  | EConstitutive _ -> "is constituted"
  | _ -> assert false

let reading_of_erule rule_id eprog erule =
  let prefix_id = Printf.sprintf "%s-%s" rule_id in
  let reading_of_imp_rule verb f g =
    reading_of_rule_if (prefix_id "if") eprog f
    ^ reading_of_rule_then (prefix_id "then") eprog verb g in
  let reading_of_exc_rule f ident =
    reading_of_rule_if (prefix_id "if") eprog f
    ^ reading_of_rule_except ident in
  match erule with
  | EObligation (f, g)
  | EPermission (f, g)
  | EConstitutive (f, g)
    -> reading_of_imp_rule (verb_of_erule erule) f g
  | EException (f, ident, _) -> reading_of_exc_rule f ident

let reading_of_doc_string = Placeholders.mark_all
