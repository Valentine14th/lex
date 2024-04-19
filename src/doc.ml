open Core
open Tlex
open Html

let html_of_trm = function
  | Formula.Term.Var x -> ident x
  | Const d -> const (Dom.to_string d)

let html_of_trms trms =
  String.concat ~sep:", " (List.map ~f:html_of_trm trms)

let paren h k x : string = if h>k then "("^x^")" else x
  
let rec html_of_formula_ l = function
  | Formula.TT -> const "true"
  | FF -> const "false"
  | EqConst (x, c) -> Printf.sprintf "%s = %s" (ident x) (const (Dom.to_string c))
  | Predicate (r, trms) -> Printf.sprintf "%s(%s)" (ident r) (html_of_trms trms)
  | Neg f -> kw "NOT" ^ html_of_formula_ 5 f
  | And (_, f, g) -> paren l 4 (html_of_formula_ 4 f ^ kw "AND" ^ html_of_formula_ 4 g)
  | Or (_, f, g) -> paren l 3 (html_of_formula_ 3 f ^ kw "OR" ^ html_of_formula_ 3 g)
  | Imp (_, f, g) -> paren l 5 (html_of_formula_ 5 f ^ kw "IMPLIES" ^ html_of_formula_ 5 g)
  | Iff (_, _, f, g) -> paren l 5 (html_of_formula_ 5 f ^ kw "EQUIV" ^ html_of_formula_ 5 g)
  | Exists (x, f) -> paren l 5 (kw "EXISTS" ^ ident x ^ kw "." ^ html_of_formula_ 5 f)
  | Forall (x, f) -> paren l 5 (kw "FORALL" ^ ident x ^ kw "." ^ html_of_formula_ 5 f)
  | Prev (i, f) -> paren l 5  (kw "PREVIOUS" ^ (interval (Interval.to_string i)) ^ html_of_formula_ 5 f)
  | Next (i, f) -> paren l 5 (kw "NEXT" ^ (interval (Interval.to_string i)) ^ html_of_formula_ 5 f)
  | Once (i, f) -> paren l 5 (kw "ONCE" ^ (interval (Interval.to_string i)) ^ html_of_formula_ 5 f)
  | Eventually (i, f) -> paren l 5 (kw "EVENTUALLY" ^ (interval (Interval.to_string i)) ^ html_of_formula_ 5 f)
  | Historically (i, f) -> paren l 5 (kw "HISTORICALLY" ^ (interval (Interval.to_string i)) ^ html_of_formula_ 5 f)
  | Always (i, f) -> paren l 5 (kw "ALWAYS" ^ (interval (Interval.to_string i)) ^ html_of_formula_ 5 f)
  | Since (_, i, f, g) -> paren l 0 (html_of_formula_ 5 f ^ kw "SINCE" ^ (interval (Interval.to_string i)) ^ html_of_formula_ 5 g)
  | Until (_, i, f, g) -> paren l 0 (html_of_formula_ 5 f ^ kw "UNTIL" ^ (interval (Interval.to_string i)) ^ html_of_formula_ 5 g)
  | Type (f, t) -> paren l 0 (html_of_formula_  5 f ^ kw ": " ^ Formula.ty_to_string t)

let html_of_formula f =
  div "lex-formula" (html_of_formula_ 0 f)
  
let html_of_trule trule =
  let string_of_imp_rule verb f g =
    div "lex-rule-if" (
        kw "whenever"
        ^ String.concat ~sep:"" (List.map ~f:html_of_formula f)
      )
    ^ div "lex-rule-then" (
          kw verb
          ^ String.concat ~sep:"" (List.map ~f:html_of_formula g)
        )
  in
  let string_of_exc_rule f id =
    div "lex-rule-if" (
        kw "whenever"
        ^ String.concat ~sep:"" (List.map ~f:html_of_formula f)
      )
    ^ div "lex-rule-then" (
          kw "except" ^ ident id
        )
  in
  match trule with
  | TObligation (f, g)
  | TPermission (f, g)
  | TConstitutive (f, g)
    -> string_of_imp_rule (verb_of_trule trule) f g
  | TException (f, ident, _) -> string_of_exc_rule f ident

let html_of_rule_type = function
  | Lex.Vanilla -> ""
  | Enforceable -> "enforceable"

let html_of_rule_constr_type = function
  | Lex.Suppressing idents -> "suppressing", idents
  | Causing idents -> "causing", idents

let html_of_rule_constr constr =
  let keyword, idents =  html_of_rule_constr_type constr in
  div "lex-rule-constr" (
      kw keyword ^ String.concat ~sep:", " (List.map ~f:ident idents)
    )
    
let html_of_rule_constrs rule_constrs =
  div "lex-rule-constrs" (
      String.concat ~sep:", " (List.map ~f:html_of_rule_constr rule_constrs)
    )

let html_of_trule_reading tprog trule = function
  | None -> 
     div "lex-rule-reading" (
         div "lex-reading-header" "Reading" 
         ^ div "lex-reading-body" (Reading.reading_of_trule tprog trule)
       )
  | Some doc_string ->
     div "lex-rule-reading" (
         div "lex-reading-header" "Reading"
         ^ ul "list-group list-group-flush" (
               li "list-group-item lex-reading-body" (Reading.reading_of_trule tprog trule)
               ^ li "list-group-item lex-docstring-body" doc_string)
       )

let html_of_doc_string s =
  div "lex-event-reading" (
      div "lex-reading-header" "Reading" 
      ^ div "lex-reading-body" (Reading.reading_of_doc_string s)
    )

let html_of_arg (_, id, ty) =
  div "lex-event-arg" (
      ident id ^ ": " ^ typ ty
    )

let html_of_args args =
  div "lex-event-args" (
      String.concat ~sep:"" (List.map ~f:html_of_arg args)
    )

let html_of_tstmt tprog =
  function
  | TSImport (_, idents, import_format) ->
     div "lex-stmt-import" (
         one_column (
             kw "import"
             ^ Lex.string_of_import_format import_format
             ^ String.concat ~sep:"." (List.map ~f:ident idents)
           )
       )
  | TSSection (section_kind, label, title) ->
     let section_class = "lex-stmt-section-" ^ Lex.string_of_section_kind section_kind in
     div section_class (
         one_column (
             span "lex-section-kind" (Lex.string_of_section_kind section_kind)
             ^ span "lex-section-label" label
             ^ (
               if String.equal title "" then
                 ""
               else
                 div "lex-section-title" title
             )
           )
       )
  | TSRule (_, _, trule, rule_type, rule_constrs, doc_string) ->
     div "lex-stmt-rule" (
         two_column (
             kw "rule"
             ^ html_of_trule trule
             ^ kw (html_of_rule_type rule_type)
             ^ (
               if List.is_empty rule_constrs then
                 ""
               else
                 html_of_rule_constrs rule_constrs
             )
           )
           (html_of_trule_reading tprog trule doc_string)
       )
  | TSEvent (name, typed_args, pol, doc_string) ->
     let html_of_event =
         kw (Lex.string_of_pol pol)
         ^ kw "event"
         ^ ident name
         ^ html_of_args typed_args
     in
     div "lex-stmt-event"
       (match doc_string with
        | Some s -> two_column html_of_event (html_of_doc_string s)
        | None   -> one_column html_of_event)
  | TSType (name, ty) ->
     div "lex-stmt-type" (
         one_column (typ name ^ kw "is" ^ typ (Lex.string_of_typ ty))
       )

let bootstrap_css_url = "https://cdn.jsdelivr.net/npm/bootstrap@5.0.2/dist/css/bootstrap.min.css"
let bootstrap_css_integrity = "sha384-EVSTQN3/azprG1Anm3QDgpJLIm9Nao0Yz1ztcQTwFspd3yD65VohhpuuCOmLASjC"
let bootstrap_link =
  Printf.sprintf
    "<link href=\"%s\" rel=\"stylesheet\" integrity=\"%s\" crossorigin=\"anonymous\">"
    bootstrap_css_url
    bootstrap_css_integrity

let html_of_tprog title css tprog =
  Printf.sprintf
    "<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>%s</title>%s<style>%s</style></head><body class=\"container\">%s</body></html>"
    title
    bootstrap_link
    css
    (
      div "lex-program" (
          String.concat ~sep:"" (List.map tprog.tstmts ~f:(html_of_tstmt tprog))
        )
    )

let print input_filename filename tprog =
  let css = In_channel.read_all (
                Filename.dirname ((Sys.get_argv ()).(0)) ^ "/../assets/lexdoc.css") in
  let html = html_of_tprog ("Lexdoc: " ^ input_filename) css tprog in
  Out_channel.write_all filename ~data:html
