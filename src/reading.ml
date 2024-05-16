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
  span "lex-formula-term" (Tformula.Term.value_to_string term)

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
    match Eformula.(f.f) with
    | Eformula.ETT -> const "true"
    | EFF -> const "false"
    | EEqConst (x, d) -> Printf.sprintf "%s is equal to %s"
                           (Tformula.Term.value_to_string x) (const (Dom.to_string d))
    | EPredicate (name, trms) as f ->
       (match Map.find Elex.(eprog.eevents) name with
        | Some (args, _, doc_string) -> 
           let names = List.map ~f:(fun (_, name, _) -> name) args in
           (match doc_string with
            | None   -> Eformula.to_string_core f
            | Some s -> Placeholders.replace_all names (List.map ~f:reading_of_term trms) s)
        | None -> Eformula.to_string_core f)
    | ENeg f ->
       "the following is not the case: "
       ^ (ul "lex-reading-neg"
            (li "lex-reading-neg-li" (reading_of_formula formula_id eprog f)))
    | EAnd (_, fs) ->
       "all of the following are the case:"
       ^ (ul "lex-reading-and"
            (String.concat
               (List.map fs ~f:(fun f -> 
                    ((li "lex-reading-and-li" (reading_of_formula formula_id eprog f)))))))
    | EOr (_, fs) ->
       "at least one of the following is the case:"
       ^ (ul "lex-reading-or"
            (String.concat
               (List.map fs ~f:(fun f -> 
                    ((li "lex-reading-and-li" (reading_of_formula formula_id eprog f)))))))
    | EImp (_, f, g) ->
       "if the following is the case:"
       ^ (ul "lex-reading-imp-left"
            (li "lex-reading-imp-left-li" (reading_of_formula formula_id eprog f)))
       ^ "then the following is the case:"
       ^ (ul "lex-reading-imp-right"
            (li "lex-reading-imp-right-li" (reading_of_formula formula_id eprog g)))
    | EIff (_, _, f, g) ->
       "the following is the case:"
       ^ (ul "lex-reading-iff-left"
            (li "lex-reading-iff-left-li" (reading_of_formula formula_id eprog f)))
       ^ "if, and only if, the following is the case:"
       ^ (ul "lex-reading-iff-right"
            (li "lex-reading-iff-right-li" (reading_of_formula formula_id eprog g)))
    | EExists (x, f) ->
       "there exists " ^ ident x ^ " such that the following is the case:"
       ^ (ul "lex-reading-exists"
            (li "lex-reading-exists-li" (reading_of_formula formula_id eprog f)))
    | EForall (x, f) ->
       "for all " ^ ident x ^ ", the following is the case:"
       ^ (ul "lex-reading-forall"
            (li "lex-reading-forall-li" (reading_of_formula formula_id eprog f)))
    | EPrev (i, f) ->
       reading_of_past_interval "at the previous time point" i
       ^ ", the following happened:"
       ^ (ul "lex-reading-prev"
            (li "lex-reading-prev-li" (reading_of_formula formula_id eprog f)))
    | ENext (i, f) ->
       reading_of_future_interval "at the next time point" i
       ^ ", the following will happen:"
       ^ (ul "lex-reading-next"
            (li "lex-reading-next-li" (reading_of_formula formula_id eprog f)))
    | EOnce (i, f) ->
       reading_of_past_interval "at some point" i
       ^ ", the following happened: "
       ^ (ul "lex-reading-once"
            (li "lex-reading-once-li" (reading_of_formula formula_id eprog f)))
    | EEventually (i, _, f) ->
       reading_of_future_interval "at some point" i
       ^ ", the following will happen: "
       ^ (ul "lex-reading-eventually"
            (li "lex-reading-eventually-li" (reading_of_formula formula_id eprog f)))
    | EHistorically (i, f) ->
       reading_of_past_interval "at all time points" i
       ^ ", the following happened: "
       ^ (ul "lex-reading-historically"
            (li "lex-reading-historically-li" (reading_of_formula formula_id eprog f)))
    | EAlways (i, _, f) ->
       reading_of_future_interval "at all time points" i
       ^ ", the following happened: "
       ^ (ul "lex-reading-always"
            (li "lex-reading-always-li" (reading_of_formula formula_id eprog f)))
    | ESince (_, i, f, g) ->
       reading_of_past_interval "at some point" i
       ^ ", the following happened: "
       ^ (ul "lex-reading-since-left"
            (li "lex-reading-since-left-li" (reading_of_formula formula_id eprog f)))
       ^ "and since then the following has always been the case:"
       ^ ", the following happened: "
       ^ (ul "lex-reading-since-right"
            (li "lex-reading-since-right-li" (reading_of_formula formula_id eprog g)))
    | EUntil (_, i, _, f, g) ->
       reading_of_future_interval "at some point" i
       ^ ", the following will happen: "
       ^ (ul "lex-reading-until-left"
            (li "lex-reading-until-left-li" (reading_of_formula formula_id eprog f)))
       ^ "and until then the following will always be the case:"
       ^ ", the following happened: "
       ^ (ul "lex-reading-until-right"
            (li "lex-reading-until-right-li" (reading_of_formula formula_id eprog g)))
    | f -> Eformula.to_string_core f in
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

let reading_of_refs labels =
    let refs = List.map labels ~f:Label.reference_of_label in
    String.concat ~sep:"\n" (List.map refs ~f:Lex.string_of_reference) (* TODO: check reading of references and possibly make additions *)

let reading_of_rule_except refs =
  p "lex-reading-then" (
      "Then "
      ^ reading_of_refs refs
      ^ " "
      ^ strong "lex-reading-verb" "does not apply"
    )

(* TODO: check if reading of scope rules is correct *)
let reading_of_rule_scope refs =
  p "lex-reading-then" (
      "Then "
      ^ reading_of_refs refs
      ^ " "
      ^ strong "lex-reading-verb" "does apply"
    )

let reading_of_type_fixes eprog rule_id type_fixes =
  let f i (ident_, ty) =
    let id = Some (Printf.sprintf "%s-fix-%d" rule_id i) in
    let fix_html =
      match Formula.TypeTerm.eval_with_doc_string Elex.(eprog.ealiases) ty with
     | (_, Some doc_string) -> ident ident_ ^ doc_string
     | (ty, None) -> ident ident_ ^ " of type " ^ typ (Dom.string_of_tt ty)
    in li ~id "lex-type-fix-reading" fix_html in
  match type_fixes with
  | [] -> ""
  | _ -> 
     p "lex-fix-reading" (
         "Fix:"
         ^ ul "lex-type-fixes-reading"
             (String.concat ~sep:"" (List.mapi ~f type_fixes))
       )

let verb_of_erule = function
  | EObligation _ -> "must happen"
  | EPermission _ -> "is permitted"
  | EConstitutive _ -> "is constituted"
  | _ -> assert false


let reading_of_erule rule_id eprog type_fixes erule =
  let prefix_id = Printf.sprintf "%s-%s" rule_id in
  let reading_of_imp_rule verb f g =
    reading_of_type_fixes eprog rule_id type_fixes
    ^ reading_of_rule_if (prefix_id "if") eprog f
    ^ reading_of_rule_then (prefix_id "then") eprog verb g in
  let reading_of_exc_rule f refs =
    reading_of_type_fixes eprog rule_id type_fixes
    ^ reading_of_rule_if (prefix_id "if") eprog f
    ^ reading_of_rule_except refs in
  let reading_of_scope_rule f refs  =
    reading_of_type_fixes eprog rule_id type_fixes
    ^ reading_of_rule_if (prefix_id "if") eprog f
    ^ reading_of_rule_scope refs in
  match erule with
  | EObligation (f, g)
  | EPermission (f, g)
  | EConstitutive (f, g)
    -> reading_of_imp_rule (verb_of_erule erule) (List.map ~f:snd f) (List.map ~f:snd g)
  | EException (f, refs, _) -> reading_of_exc_rule (List.map ~f:snd f) (List.map ~f:snd refs)
  | EScope (f, refs, _) -> reading_of_scope_rule (List.map ~f:snd f) (List.map ~f:snd refs)

let reading_of_doc_string = Placeholders.mark_all
