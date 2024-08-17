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

let rec html_of_trm ?(l=0) = function
  | Tformula.TTerm.TVar x -> ident x
  | TConst d -> const (Dom.to_string d)
  | TApp (f, trms) -> Printf.sprintf "%s(%s)" f (html_of_trms trms)
  | TUnop (o, t) -> Printf.sprintf (Util.paren l 10 "%s %s")
                     (Formula.Term.string_of_unop o)
                     (html_of_trm ~l:10 t.trm)
  | TBinop (t, o, t') -> let l' = Formula.Term.prio_of_binop o in
                        Printf.sprintf (Util.paren l l' "%s %s %s")
                          (html_of_trm ~l:l' t.trm)
                          (Formula.Term.string_of_binop o)
                          (html_of_trm ~l:l' t'.trm)
  | TProj (t, p) -> Printf.sprintf "%s.%s" (html_of_trm ~l:10 t.trm) p
  | TRecord kvs ->
     let f (k, v) = k ^ " : " ^ html_of_trm Tformula.TTerm.(v.trm) in
     Printf.sprintf "{ %s }" (String.concat ~sep:", " (List.map kvs ~f))

and html_of_trms trms = String.concat ~sep:", " (List.map trms ~f:(fun t -> html_of_trm t.trm))

let reading_of_unop = function
  | Formula.Term.UNot -> "not"
  | USub -> "minus"

let reading_of_binop = function
  | Formula.Term.BAdd -> "plus"
  | BSub -> "minus"
  | BMul -> "multiplied by"
  | BDiv -> "divided by"
  | BPow -> "to the power of"
  | BAnd -> "and"
  | BOr  -> "or"
  | BXor -> "exclusive-or"
  | BEq  -> "is equal to"
  | BNeq -> "is not equal to"
  | BLt  -> "is less than"
  | BLeq -> "is less or equal to"
  | BGt  -> "is greater than"
  | BGeq -> "is greater or equal to"

let reading_of_dom = function
  | Dom.Int v -> Int.to_string v
  | Str v -> String.to_string v
  | Float v -> Float.to_string v
  | Bool v -> Bool.to_string v
  | Time v -> Lextime.Time.to_string v
  | Span v -> Lextime.Span.to_string_reading v
  | Money v -> Money.to_string_reading v

let rec reading_of_trm ?(l=0) eprog = function
  | Tformula.TTerm.TVar x -> ident x
  | TConst d -> const (reading_of_dom d)
  | TApp (f, trms) ->
     (match Map.find Elex.(eprog.efunctions) f with
      | Some (args, _, Some s) ->
         let names = List.map ~f:(fun (name, _) -> name) args in
         Placeholders.replace_all names (List.map ~f:(reading_of_term eprog) trms) s
      | _ -> Printf.sprintf "%s(%s)" f (html_of_trms trms))
  | TUnop (o, t) -> Printf.sprintf (Util.paren l 10 "%s %s")
                     (reading_of_unop o)
                     (reading_of_trm ~l:10 eprog t.trm)
  | TBinop (t, o, t') -> let l' = Formula.Term.prio_of_binop o in
                        Printf.sprintf (Util.paren l l' "%s %s %s")
                          (reading_of_trm ~l:l' eprog t.trm)
                          (reading_of_binop o)
                          (reading_of_trm ~l:l' eprog t'.trm)
  | TProj (t, p) -> Printf.sprintf "the field %s of %s" p (html_of_trm ~l:10 t.trm) 
  | TRecord kvs ->
     let f (k, v) =
       li "lex-reading-record-field"
         (ident k ^ " is equal to " ^ reading_of_trm eprog Tformula.TTerm.(v.trm)) in
     "a record where" ^ ul "lex-reading-record" (String.concat (List.map kvs ~f))


and reading_of_term eprog term =
  span "" (reading_of_trm eprog Tformula.TTerm.(term.trm))

let reading_of_span span = const (Lextime.Span.to_string_reading span)

let reading_of_past_interval default = function
  | Interval.U (C s) when Lextime.Span.is_zero s -> default  ^ " in the past"
  | U (C s) -> Printf.sprintf "%s at least %s ago" default (reading_of_span s)
  | U (O s) -> Printf.sprintf "%s strictly more than %s ago" default (reading_of_span s)
  | B (C ls, C rs) when Lextime.Span.is_zero ls -> Printf.sprintf "%s within %s (included) in the past" default (reading_of_span rs)
  | B (C ls, O rs) when Lextime.Span.is_zero ls -> Printf.sprintf "%s within %s (excluded) in the past" default (reading_of_span rs)
  | B (C ls, C rs) -> Printf.sprintf "%s between %s (included) and %s (included) ago" default (reading_of_span ls) (reading_of_span rs)
  | B (C ls, O rs) -> Printf.sprintf "%s between %s (included) and %s (excluded) ago" default (reading_of_span ls) (reading_of_span rs)
  | B (O ls, C rs) -> Printf.sprintf "%s between %s (excluded) and %s (included) ago" default (reading_of_span ls) (reading_of_span rs)
  | B (O ls, O rs) -> Printf.sprintf "%s between %s (excluded) and %s (excluded) ago" default (reading_of_span ls) (reading_of_span rs)

let reading_of_future_interval default = function
  | Interval.U (C s) when Lextime.Span.is_zero s -> default ^ " in the future"
  | U (C s) -> Printf.sprintf "%s in at least %s" default (reading_of_span s)
  | U (O s) -> Printf.sprintf "%s in strictly more than %s" default (reading_of_span s)
  | B (C ls, C rs) when Lextime.Span.is_zero ls -> Printf.sprintf "%s within %s (included) in the future" default (reading_of_span rs)
  | B (C ls, O rs) when Lextime.Span.is_zero ls -> Printf.sprintf "%s within %s (excluded) in the future" default (reading_of_span rs)
  | B (C ls, C rs) -> Printf.sprintf "%s in between %s (included) and %s (included) ago" default (reading_of_span ls) (reading_of_span rs)
  | B (C ls, O rs) -> Printf.sprintf "%s in between %s (included) and %s (excluded) ago" default (reading_of_span ls) (reading_of_span rs)
  | B (O ls, C rs) -> Printf.sprintf "%s in between %s (excluded) and %s (included) ago" default (reading_of_span ls) (reading_of_span rs)
  | B (O ls, O rs) -> Printf.sprintf "%s in between %s (excluded) and %s (excluded) ago" default (reading_of_span ls) (reading_of_span rs)

let reading_of_op = function
  | Aggregation.ASum -> "sum"
  | AAvg -> "average"
  | AMed -> "median"
  | ACnt -> "count"
  | AMin -> "minimum"
  | AMax -> "maximum"

let rec reading_of_formula formula_id eprog f =
  let inner_html = 
    match Eformula.(f.f) with
    | Eformula.ETT -> const "true"
    | EFF -> const "false"
    | EEqConst (x, (Dom.Bool true, _)) -> reading_of_term eprog x
    | EEqConst (x, (d, _)) ->
       Printf.sprintf "%s is equal to %s" (reading_of_term eprog x) (const (reading_of_dom d))
    | EPredicate (name, trms, event_type) as g ->
       (match Map.find Elex.(eprog.eevents) name with
        | Some (_, args, _, doc_string) -> 
           let names = List.map ~f:(fun (_, name, _) -> name) args in
           (match doc_string, event_type with
            | None, _ -> Formula.to_string (Eformula.to_formula f)
            | Some s, Event (_, Functional) ->
               Printf.sprintf "%s is equal to %s"
                 (Placeholders.replace_all (List.drop_last_exn names)
                    (List.map ~f:(reading_of_term eprog) (List.drop_last_exn trms)) s)
                 (reading_of_term eprog (List.last_exn trms))
            | Some s, Event (_, Variable) ->
               Printf.sprintf "%s is equal to %s"
                 s
                 (reading_of_term eprog (List.last_exn trms))
            | Some s, _ -> Placeholders.replace_all names (List.map ~f:(reading_of_term eprog) trms) s)
        | None -> Eformula.to_string_core g)
    | EAgg (s, op, x, y, f) ->
       let reading_of_groupby =
         if List.is_empty y then
            ""
          else
            ", grouping on " ^ String.concat ~sep:", " (List.map y ~f:ident) ^ ", " in
       ident s
       ^ " is the "
       ^ reading_of_op op
       ^ " of all "
       ^ reading_of_term eprog x
       ^ reading_of_groupby
       ^ " such that the following is the case:"
       ^ (ul "lex-reading-neg"
            (li "lex-reading-neg-li" (reading_of_formula formula_id eprog f)))
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
    | _ -> Formula.to_string (Eformula.to_formula f) in
  let id = Some (Printf.sprintf "%s-%d" formula_id f.id) in
  div ~id "lex-subformula-reading" inner_html

let reading_of_pattern formula_id eprog = function
  | EPPresent -> ""
  | EPEventually i -> reading_of_future_interval "at some point" i
  | EPAlways i -> reading_of_future_interval "at all time points" i
  | EPUntil (i, f) -> reading_of_future_interval "at some point" i
                      ^ "delaying while"
                      ^ reading_of_formula formula_id eprog f
  | EPOnce i -> reading_of_future_interval "at some point" i
  | EPHistorically i -> reading_of_future_interval "at all time points" i
  | EPSince (i, f) -> reading_of_future_interval "at all times point" i
                      ^ "since"
                      ^ reading_of_formula formula_id eprog f


let reading_of_rule_if prefix_id eprog pf =
  let formula_id = Printf.sprintf "%s-%d" prefix_id in
  let f i g =
    li "lex-reading-if-formula" (reading_of_formula (formula_id i) eprog g) in
  p "lex-reading-if" (
      "Whenever all of the following happen"
      ^ reading_of_pattern "if-since" eprog pf.p
      ^ ":"
      ^ ul "lex-reading-if-formulae"
          (String.concat ~sep:"" (List.mapi ~f pf.fs))
    )

let reading_of_rule_then prefix_id eprog verb pf =
  let formula_id = Printf.sprintf "%s-%d" prefix_id in
  let f i g =
    li "lex-reading-then-formula" (reading_of_formula (formula_id i) eprog g) in
  p "lex-reading-then" (
      "Then the following "
      ^ strong "lex-reading-verb" verb
      ^ reading_of_pattern "if-then" eprog pf.p
      ^ ":"
      ^ ul "lex-reading-then-formulae"
          (String.concat ~sep:"" (List.mapi ~f pf.fs))
    )

let reading_of_rule_then2 prefix_id eprog g =
  let formula_id = Printf.sprintf "%s-%d" prefix_id in
  let f i g =
    li "lex-reading-then-formula" (reading_of_formula (formula_id i) eprog g) in
  p "lex-reading-then" (
      "Instead, the following "
      ^ strong "lex-reading-verb" "shall be constituted"
      ^ ":"
      ^ ul "lex-reading-then-formulae"
          (String.concat ~sep:"" (List.mapi ~f g))
    )

let reading_of_reference (eref: eref_expr) =
  let l = eref.label in
  let rs = eref.ref.sks in
  let rule = eref.ref.rule in
  let rule_id = match rule with
    | Some r -> " " ^ span "lex-section-kind" "rule" ^ r
    | None ->  "" in
  let reading_of_section_kind_and_name (s, n) =
    span "lex-section-kind" (Lex.string_of_section_kind s) ^ n in
  a ("#lex-section-" ^ Label.doc_id l) "lex-section-link"
    (String.concat ~sep:" " (List.map ~f:reading_of_section_kind_and_name rs) ^ rule_id)

(* let reading_of_ref ref_id (l, r) = *)
let reading_of_ref ref_id (eref: eref_expr) =
  span "lex-subformula-reading" ~id:(Some ref_id) (reading_of_reference eref)

let reading_of_rule_except prefix_id (refs: eref_expr list) =
  let ref_id = Printf.sprintf "%s-%d" prefix_id in
  let f i r =
    li "lex-reading-then-formula" (reading_of_ref (ref_id i) r) in
  match List.length refs with
  | 1 ->
     p "lex-reading-then" (
         "Then "
         ^ span "lex-reading-then-formula" (reading_of_ref (ref_id 0) (List.hd_exn refs))
         ^ " " ^ strong "lex-reading-verb" "shall not apply" ^ "."
       )
  | _ -> 
     p "lex-reading-then" (
         "Then the following "
         ^ strong "lex-reading-verb" "shall not apply"
         ^ ":"
         ^ ul "lex-reading-then-formulae"
             (String.concat ~sep:"" (List.mapi ~f refs))
       )

(* TODO: check if reading of scope rules is correct *)
let reading_of_rule_scope prefix_id refs =
  let suffix = match List.length refs with
  | 1 -> "apply"
  | _ -> "applies" in
  let ref_id = Printf.sprintf "%s-%d" prefix_id in
  let f i r =
    li "lex-reading-then-formula" (reading_of_ref (ref_id i) r) in
  p "lex-reading-then" (
      "Then the following "
      ^ strong "lex-reading-verb" suffix
      ^ ":"
      ^ ul "lex-reading-then-formulae"
          (String.concat ~sep:"" (List.mapi ~f refs))
    )

let reading_of_type_fixes eprog rule_id type_fixes =
  let f i (ident_, ty) =
    let id = Some (Printf.sprintf "%s-fix-%d" rule_id i) in
    let fix_html =
      match Formula.TypeTerm.eval_with_doc_string Elex.(eprog.ealiases) ty with
     | (_, Some doc_string) -> ident ident_ ^ doc_string
     | (ty_string, None) -> ident ident_ ^ " of type " ^ typ ty_string
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
  | EObligation _ -> "shall be obligatory"
  | EPermission _ -> "shall be permitted"
  | EConstitutive _ -> "shall be constituted"
  | _ -> assert false


let reading_of_erule rule_id eprog type_fixes erule =
  let prefix_id = Printf.sprintf "%s-%s" rule_id in
  (* let reading_of_imp_rule verb f p g q rcs rt = *)
  let reading_of_imp_rule verb pf1 pf2 _ _ =
    reading_of_type_fixes eprog rule_id type_fixes
    ^ reading_of_rule_if (prefix_id "if") eprog pf1
    ^ reading_of_rule_then (prefix_id "then") eprog verb pf2 in
  let reading_of_cons_rule verb pf g =
    reading_of_type_fixes eprog rule_id type_fixes
    ^ reading_of_rule_if (prefix_id "if") eprog pf
    ^ reading_of_rule_then (prefix_id "then") eprog verb { fs=g; p=EPPresent} in
  let reading_of_exc_rule pf refs =
    reading_of_type_fixes eprog rule_id type_fixes
    ^ reading_of_rule_if (prefix_id "if") eprog pf
    ^ reading_of_rule_except (prefix_id "then") refs in
  let reading_of_excc_rule pf refs g =
    reading_of_type_fixes eprog rule_id type_fixes
    ^ reading_of_rule_if (prefix_id "if") eprog pf 
    ^ reading_of_rule_except (prefix_id "then") refs
    ^ reading_of_rule_then2 (prefix_id "then2") eprog g in
  let reading_of_scope_rule pf refs =
    reading_of_type_fixes eprog rule_id type_fixes
    ^ reading_of_rule_if (prefix_id "if") eprog pf
    ^ reading_of_rule_scope (prefix_id "then") refs in
  match erule with
  | EObligation _ ->
    let pf1, pf2, rt, rcs = get_obligation_params eprog.ecrules erule in
    reading_of_imp_rule (verb_of_erule erule) pf1 pf2 rcs rt
  | EPermission _ ->
    let pf1, pf2, rt, rcs = get_permission_params eprog.ecrules erule in
    reading_of_imp_rule (verb_of_erule erule) pf1 pf2 rcs rt
  | EConstitutive _ ->
    let pf, g = get_constitutive_params eprog.ecrules erule in
    reading_of_cons_rule (verb_of_erule erule) pf g
  | EException _ ->
    let pf, refs = get_exception_params eprog.ecrules erule in
    reading_of_exc_rule pf refs
  | EExceptionC _ ->
    let pf, refs, g = get_exceptionc_params eprog.ecrules erule in
    reading_of_excc_rule pf refs g
  | EScope _ ->
    let pf, refs = get_scope_params eprog.ecrules erule in
    reading_of_scope_rule pf refs

let reading_of_doc_string = Placeholders.mark_all
