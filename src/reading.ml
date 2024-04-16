open Core
open Lex
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
    
let rec reading_of_formula tprog = function
  | Formula.TT -> const "true"
  | FF -> const "false"
  | EqConst (x, d) -> ident x ^ " is equal to " ^ const (Dom.to_string d)
  | Predicate (name, trms) as f ->
    (match Map.find Tlex.(tprog.tevents) name with
     | Some (args, _, doc_string) -> 
        let names = List.map ~f:(fun (_, name, _) -> name) args in
        (match doc_string with
         | None   -> Formula.to_string f
         | Some s -> Placeholders.replace_all names (List.map ~f:reading_of_term trms) s)
     | None -> Formula.to_string f)
  | Neg f ->
     "the following is not the case: "
     ^ (ul "lex-reading-neg"
          (li "lex-reading-neg-li" (reading_of_formula tprog f)))
  | And (_, f, g) ->
     "all of the following are the case:"
     ^ (ul "lex-reading-and"
          ((li "lex-reading-and-li" (reading_of_formula tprog f))
           ^ (li "lex-reading-and-li" (reading_of_formula tprog g))))
  | Or (_, f, g) ->
     "at least one of the following is the case:"
     ^ (ul "lex-reading-or"
          ((li "lex-reading-or-li" (reading_of_formula tprog f))
           ^ (li "lex-reading-or-li" (reading_of_formula tprog g))))
  | Imp (_, f, g) ->
     "if the following is the case:"
     ^ (ul "lex-reading-imp-left"
          (li "lex-reading-imp-left-li" (reading_of_formula tprog f)))
     ^ "then the following is the case:"
     ^ (ul "lex-reading-imp-right"
          (li "lex-reading-imp-right-li" (reading_of_formula tprog g)))
  | Iff (_, _, f, g) ->
     "the following is the case:"
     ^ (ul "lex-reading-iff-left"
          (li "lex-reading-iff-left-li" (reading_of_formula tprog f)))
     ^ "if, and only if, the following is the case:"
     ^ (ul "lex-reading-iff-right"
          (li "lex-reading-iff-right-li" (reading_of_formula tprog g)))
  | Exists (x, f) ->
     "there exists " ^ ident x ^ " such that the following is the case:"
     ^ (ul "lex-reading-exists"
          (li "lex-reading-exists-li" (reading_of_formula tprog f)))
  | Forall (x, f) ->
     "for all " ^ ident x ^ ", the following is the case:"
     ^ (ul "lex-reading-forall"
          (li "lex-reading-forall-li" (reading_of_formula tprog f)))
  | Prev (i, f) ->
     reading_of_past_interval "at the previous time point" i
     ^ ", the following happened:"
     ^ (ul "lex-reading-prev"
          (li "lex-reading-prev-li" (reading_of_formula tprog f)))
  | Next (i, f) ->
     reading_of_future_interval "at the next time point" i
     ^ ", the following will happen:"
     ^ (ul "lex-reading-next"
          (li "lex-reading-next-li" (reading_of_formula tprog f)))
  | Once (i, f) ->
     reading_of_past_interval "at some point" i
     ^ ", the following happened: "
     ^ (ul "lex-reading-once"
          (li "lex-reading-once-li" (reading_of_formula tprog f)))
  | Eventually (i, f) ->
     reading_of_future_interval "at some point" i
     ^ ", the following will happen: "
     ^ (ul "lex-reading-eventually"
          (li "lex-reading-eventually-li" (reading_of_formula tprog f)))
  | Historically (i, f) ->
     reading_of_past_interval "at all time points" i
     ^ ", the following happened: "
     ^ (ul "lex-reading-historically"
          (li "lex-reading-historically-li" (reading_of_formula tprog f)))
  | Always (i, f) ->
     reading_of_future_interval "at all time points" i
     ^ ", the following happened: "
     ^ (ul "lex-reading-always"
          (li "lex-reading-always-li" (reading_of_formula tprog f)))
  | Since (_, i, f, g) ->
     reading_of_past_interval "at some point" i
     ^ ", the following happened: "
     ^ (ul "lex-reading-since-left"
          (li "lex-reading-since-left-li" (reading_of_formula tprog f)))
     ^ "and since then the following has always been the case:"
     ^ ", the following happened: "
     ^ (ul "lex-reading-since-right"
          (li "lex-reading-since-right-li" (reading_of_formula tprog g)))
  | Until (_, i, f, g) ->
     reading_of_future_interval "at some point" i
     ^ ", the following will happen: "
     ^ (ul "lex-reading-until-left"
          (li "lex-reading-until-left-li" (reading_of_formula tprog f)))
     ^ "and until then the following will always be the case:"
     ^ ", the following happened: "
     ^ (ul "lex-reading-until-right"
          (li "lex-reading-until-right-li" (reading_of_formula tprog g)))
  | f -> Formula.to_string f

let reading_of_rule_if tprog g =
  let f g = li "lex-reading-if-formula" (reading_of_formula tprog g) in
    p "lex-reading-if" (
        "Whenever all of the following happen:"
        ^ ul "lex-reading-if-formulae"
            (String.concat ~sep:"" (List.map ~f g))
      )

let reading_of_rule_then tprog verb g =
  let f g = li "lex-reading-then-formula" (reading_of_formula tprog g) in
  p "lex-reading-then" (
      "Then the following "
      ^ strong "lex-reading-verb" verb
      ^ ":"
      ^ ul "lex-reading-then-formulae"
          (String.concat ~sep:"" (List.map ~f g))
    )

let reading_of_rule_except ident =
  p "lex-reading-then" (
      "rule " ^ ident ^ " does not apply"
    )

let verb_of_rule = function
  | Obligation _ -> "must happen"
  | Permission _ -> "is permitted"
  | Constitutive _ -> "is constituted"
  | _ -> assert false

let reading_of_rule tprog rule =
  let reading_of_imp_rule verb f g =
    reading_of_rule_if tprog f ^ reading_of_rule_then tprog verb g in
  let reading_of_exc_rule f ident =
    reading_of_rule_if tprog f ^ reading_of_rule_except ident in
  match rule with
  | Obligation (f, g) | Permission (f, g) | Constitutive (f, g)
    -> reading_of_imp_rule (verb_of_rule rule) f g
  | Exception (f, ident) -> reading_of_exc_rule f ident

let reading_of_doc_string = Placeholders.mark_all
