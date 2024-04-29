open Core
open Elex
open Html
open Tformula

let html_of_trm = function
  | Formula.Term.Var x -> ident x
  | Const d -> const (Dom.to_string d)

let html_of_trms trms =
  String.concat ~sep:", " (List.map ~f:html_of_trm trms)

let rec html_of_formula_ formula_id l f =
  let inner_html = 
    match f.f with
    | TTT -> const "true"
    | TFF -> const "false"
    | TEqConst (x, c) -> Printf.sprintf "%s = %s" (ident x) (const (Dom.to_string c))
    | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" (ident r) (html_of_trms trms)
    | TNeg f -> kw "NOT" ^ html_of_formula_ formula_id 5 f
    | TAnd (_, fs) -> Util.paren_string l 4 (
                          String.concat ~sep:(kw "AND") (List.map fs ~f:(html_of_formula_ formula_id 4)))
    | TOr (_, fs) -> Util.paren_string l 3 (
                         String.concat ~sep:(kw "OR") (List.map fs ~f:(html_of_formula_ formula_id 3)))
    | TImp (_, f, g) -> Util.paren_string l 5 (html_of_formula_ formula_id 5 f ^ kw "IMPLIES" ^ html_of_formula_ formula_id 5 g)
    | TIff (_, _, f, g) -> Util.paren_string l 5 (html_of_formula_ formula_id 5 f ^ kw "EQUIV" ^ html_of_formula_ formula_id 5 g)
    | TExists (x, f) -> Util.paren_string l 5 (kw "EXISTS" ^ ident x ^ kw "." ^ html_of_formula_ formula_id 5 f)
    | TForall (x, f) -> Util.paren_string l 5 (kw "FORALL" ^ ident x ^ kw "." ^ html_of_formula_ formula_id 5 f)
    | TPrev (i, f) -> Util.paren_string l 5  (kw "PREVIOUS" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | TNext (i, f) -> Util.paren_string l 5 (kw "NEXT" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | TOnce (i, f) -> Util.paren_string l 5 (kw "ONCE" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | TEventually (i, _, f) -> Util.paren_string l 5 (kw "EVENTUALLY" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | THistorically (i, f) -> Util.paren_string l 5 (kw "HISTORICALLY" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | TAlways (i, _, f) -> Util.paren_string l 5 (kw "ALWAYS" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | TSince (_, i, f, g) -> Util.paren_string l 0 (html_of_formula_ formula_id 5 f ^ kw "SINCE" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 g)
    | TUntil (_, i, _, f, g) -> Util.paren_string l 0 (html_of_formula_ formula_id 5 f ^ kw "UNTIL" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 g)
    | TType (f, t) -> Util.paren_string l 0 (html_of_formula_ formula_id  5 f ^ kw ": " ^ Formula.ty_to_string t) in
  let id = Some (Printf.sprintf "%s-%d" formula_id f.id) in
  span ~id "lex-subformula" inner_html 

let html_of_formula formula_id f =
  div "lex-formula" (html_of_formula_ formula_id 0 f)
  
let html_of_erule rule_id erule =
  let formula_id infix =
    Printf.sprintf "%s-%s-%d" rule_id infix in
  let string_of_imp_rule verb f g =
    div "lex-rule-if" (
        kw "whenever"
        ^ String.concat ~sep:"" (List.mapi ~f:(fun i f -> html_of_formula (formula_id "if" i) f) f)
      )
    ^ div "lex-rule-then" (
          kw verb
          ^ String.concat ~sep:"" (List.mapi ~f:(fun i f -> html_of_formula (formula_id "then" i) f) g)
        )
  in
  let string_of_exc_rule f id =
    div "lex-rule-if" (
        kw "whenever"
        ^ String.concat ~sep:"" (List.mapi ~f:(fun i f -> html_of_formula (formula_id "if" i) f) f)
      )
    ^ div "lex-rule-then" (
          kw "except" ^ ident id
        )
  in
  match erule with
  | EObligation (f, g)
  | EPermission (f, g)
  | EConstitutive (f, g)
    -> string_of_imp_rule (verb_of_erule erule) f g
  | EException (f, ident, _) -> string_of_exc_rule f ident

let html_of_rule_type = function
  | Lex.Vanilla -> ""
  | Enforceable -> "enforceable"
  | Transparent -> "transUtil.paren_stringtly enforceable"

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

let html_of_tannot = function
  | Tlex.TALex s -> s
  | TAFormex (m, s) -> Html.formex m ^ s

let html_of_erule_reading rule_id eprog type_fixes erule = function
  | None -> 
     div "lex-rule-reading" (
         div "lex-reading-header" "Reading" 
         ^ div "lex-reading-body" (Reading.reading_of_erule rule_id eprog type_fixes erule)
       )
  | Some doc_string ->
     div "lex-rule-reading" (
         div "lex-reading-header" "Reading"
         ^ ul "list-group list-group-flush" (
               li "list-group-item lex-reading-body" (Reading.reading_of_erule rule_id eprog type_fixes erule)
               ^ li "list-group-item lex-docstring-body" (html_of_tannot doc_string))
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

let html_of_type_fix rule_id i (ident_, typ_) =
  let id = Some (Printf.sprintf "%s-fix-%d" rule_id i) in
  div "lex-type-fix-outer" (
      span ~id "lex-type-fix" (ident ident_ ^ ": " ^ typ typ_)
    )

let html_of_args args =
  div "lex-event-args" (
      String.concat ~sep:"" (List.map ~f:html_of_arg args)
    )

let html_of_type_fixes rule_id = function
  | [] -> ""
  | type_fixes -> 
     div "lex-type-fixes" (
         kw "fix" ^ String.concat ~sep:"" (List.mapi ~f:(html_of_type_fix rule_id) type_fixes)
       )

let html_of_estmt eprog =
  function
  | ESImport (_, idents, import_format) ->
     div "lex-stmt-import" (
         one_column (
             kw "import"
             ^ kw (Lex.string_of_import_format import_format)
             ^ String.concat ~sep:"." (List.map ~f:ident idents)
           )
       )
  | ESSection (section_kind, _, label, title) ->
     let section_class = "lex-stmt-section-" ^ Lex.string_of_section_kind section_kind in
     div section_class (
         one_column (
             span "lex-section-kind" (Lex.string_of_section_kind section_kind)
             ^ span "lex-section-label" label
             ^ (
               match title with
               | Some title -> div "lex-section-title" (html_of_tannot title)
               | None -> ""
             )
           )
       )
  | ESRule (_, label, type_fixes, erule, rule_type, rule_constrs, doc_string) ->
    let module Convention = (val eprog.labelconvention : Label.LabelConvention) in
    let qualified_id = Convention.convention.qualified_id in
    let rule_id = qualified_id label in
    div "lex-stmt-rule" (
        two_column (
            kw "rule"
            ^ html_of_type_fixes ("lex-subformula-" ^ rule_id) type_fixes
            ^ html_of_erule ("lex-subformula-" ^ rule_id) erule
            ^ kw (html_of_rule_type rule_type)
            ^ (
              if List.is_empty rule_constrs then
                ""
              else
                html_of_rule_constrs rule_constrs
            )
          )
          (html_of_erule_reading ("lex-subformula-reading-" ^ rule_id) eprog type_fixes erule doc_string)
      )
  | ESEvent (event_type, name, typed_args, pol, doc_string) ->
     let html_of_event =
         kw (Lex.string_of_pol pol)
         ^ kw (Lex.string_of_event_type event_type)
         ^ ident name
         ^ html_of_args typed_args
     in
     div "lex-stmt-event"
       (match doc_string with
        | Some s -> two_column html_of_event (html_of_doc_string s)
        | None   -> one_column html_of_event)
  | ESType (name, ty, doc_string) ->
     let html_of_type = typ name ^ kw "is" ^ typ (Lex.string_of_typ ty) in
     div "lex-stmt-type"
       (match doc_string with
        | Some s -> two_column html_of_type (html_of_doc_string s)
        | None   -> one_column html_of_type)
  | ESNote text ->
     div "lex-stmt-note" (
         one_column (kw "note" ^ string text)
       )

let bootstrap_css_url = "https://cdn.jsdelivr.net/npm/bootstrap@5.0.2/dist/css/bootstrap.min.css"
let bootstrap_css_integrity = "sha384-EVSTQN3/azprG1Anm3QDgpJLIm9Nao0Yz1ztcQTwFspd3yD65VohhpuuCOmLASjC"
let bootstrap_link =
  Printf.sprintf
    "<link href=\"%s\" rel=\"stylesheet\" integrity=\"%s\" crossorigin=\"anonymous\">"
    bootstrap_css_url
    bootstrap_css_integrity
let jquery_url = "https://cdn.jsdelivr.net/npm/jquery@3.7.1/dist/jquery.min.js"
let jquery_link =
  Printf.sprintf
    "<script src=\"%s\"></script>"
    jquery_url

let html_of_eprog title css js eprog =
  Printf.sprintf
    "<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>%s</title>%s<style>%s</style></head><body class=\"container\">%s</body>%s<script>%s</script></html>"
    title
    bootstrap_link
    css
    (
      div "lex-program" (
          String.concat ~sep:"" (List.map eprog.estmts ~f:(html_of_estmt eprog))
        )
    )
    jquery_link
    js

let to_file input_filename filename eprog =
  let css = In_channel.read_all (
                Filename.dirname ((Sys.get_argv ()).(0)) ^ "/../assets/lexdoc.css") in
  let js = In_channel.read_all (
                Filename.dirname ((Sys.get_argv ()).(0)) ^ "/../assets/lexdoc.js") in
  let html = html_of_eprog ("Lexdoc: " ^ input_filename) css js eprog in
  print_endline filename;
  Out_channel.write_all filename ~data:html
