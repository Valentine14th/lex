open Core
open Elex
open Html
open Eformula


let rec html_of_trm ?(l=0) = function
  | Tformula.Term.TVar x -> ident x
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

and html_of_trms trms = String.concat ~sep:", " (List.map trms ~f:(fun t -> html_of_trm t.trm))

let rec html_of_formula_ formula_id l f =
  let inner_html = 
    match f.f with
    | ETT -> const "true"
    | EFF -> const "false"
    | EEqConst (x, c) -> Printf.sprintf "{%s = %s}" (html_of_trm x.trm) (const (Dom.to_string c))
    | EPredicate (r, trms) -> Printf.sprintf "%s(%s)" (ident r) (html_of_trms trms)
    | EAgg (s, op, x, y, f) ->
       Printf.sprintf "{%s = %s(%s; %s; %s)}"
         (ident s) (kw (Aggregation.op_to_string op)) (html_of_trm x.trm)
         (String.concat ~sep:","  (List.map y ~f:ident)) (html_of_formula_ formula_id 5 f)
    | ENeg f -> kw "NOT" ^ html_of_formula_ formula_id 5 f
    | EAnd (_, fs) -> Util.paren_string l 4 (
                          String.concat ~sep:(kw "AND") (List.map fs ~f:(html_of_formula_ formula_id 4)))
    | EOr (_, fs) -> Util.paren_string l 3 (
                         String.concat ~sep:(kw "OR") (List.map fs ~f:(html_of_formula_ formula_id 3)))
    | EImp (_, f, g) -> Util.paren_string l 5 (html_of_formula_ formula_id 5 f ^ kw "IMPLIES" ^ html_of_formula_ formula_id 5 g)
    | EIff (_, _, f, g) -> Util.paren_string l 5 (html_of_formula_ formula_id 5 f ^ kw "EQUIV" ^ html_of_formula_ formula_id 5 g)
    | EExists (x, f) -> Util.paren_string l 5 (kw "EXISTS" ^ ident x ^ kw "." ^ html_of_formula_ formula_id 5 f)
    | EForall (x, f) -> Util.paren_string l 5 (kw "FORALL" ^ ident x ^ kw "." ^ html_of_formula_ formula_id 5 f)
    | EPrev (i, f) -> Util.paren_string l 5  (kw "PREVIOUS" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | ENext (i, f) -> Util.paren_string l 5 (kw "NEXT" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | EOnce (i, f) -> Util.paren_string l 5 (kw "ONCE" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | EEventually (i, _, f) -> Util.paren_string l 5 (kw "EVENTUALLY" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | EHistorically (i, f) -> Util.paren_string l 5 (kw "HISTORICALLY" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | EAlways (i, _, f) -> Util.paren_string l 5 (kw "ALWAYS" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 f)
    | ESince (_, i, f, g) -> Util.paren_string l 0 (html_of_formula_ formula_id 5 f ^ kw "SINCE" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 g)
    | EUntil (_, i, _, f, g) -> Util.paren_string l 0 (html_of_formula_ formula_id 5 f ^ kw "UNTIL" ^ (interval (Interval.to_string i)) ^ html_of_formula_ formula_id 5 g)
    | EType (f, t) -> Util.paren_string l 0 (html_of_formula_ formula_id  5 f ^ kw ": " ^ Formula.ty_to_string t) in
  let id = Some (Printf.sprintf "%s-%d" formula_id f.id) in
  span ~id "lex-subformula" inner_html 

let html_of_formula formula_id f =
  div "lex-formula" (html_of_formula_ formula_id 0 f)

let html_of_span s = const (Lextime.Span.to_string s)

let html_of_interval future = function
  | Interval.U (C s) when Interval.is_zero s -> ""
  | U (C s) ->
     (if future then kw "after" else kw "before") ^ html_of_span s
  | U (O s) ->
     kw "strictly" ^ (if future then kw "after" else kw "before") ^ html_of_span s
  | B (C ls, C rs) when Interval.is_zero ls -> kw "within" ^ html_of_span rs
  | B (C ls, C rs) ->
     kw "between" ^ html_of_span ls ^ kw "and" ^ html_of_span rs
  | B (O ls, O rs) ->
     kw "strictly" ^ kw "between" ^ html_of_span ls ^ kw "and" ^ html_of_span rs
  | B (C ls, O rs) ->
     kw "between" ^ html_of_span ls ^ kw "and" ^ html_of_span rs ^ kw "excluded"
  | B (O ls, C rs) ->
     kw "between" ^ html_of_span ls ^ kw "excluded" ^ kw "and" ^ html_of_span rs
    

let html_of_pattern formula_id = function
  | EPPresent -> ""
  | EPEventually i -> kw "eventually"
                      ^ html_of_interval true i
  | EPAlways i -> kw "always" ^ kw "in" ^ kw "the" ^ kw "past"
                  ^ html_of_interval true i
  | EPUntil (i, f) -> kw "eventually" ^ kw "delaying" ^ kw "if"
                      ^ html_of_formula formula_id f
                      ^ html_of_interval true i
  | EPOnce i -> kw "once"
                ^ html_of_interval false i
  | EPHistorically i -> kw "always" ^ kw "in" ^ kw "the" ^ kw "future"
                        ^ html_of_interval false i
  | EPSince (i, f) -> kw "always" ^ kw "since"
                      ^ html_of_formula formula_id f
                      ^ html_of_interval false i

let section_id rs =
  "lex-section-" ^ String.concat ~sep:"-" (List.map ~f:(fun (s, n) -> Lex.string_of_section_kind s ^ "-" ^ n) rs)

let html_of_reference (l, (rs, rule)) =
  let rule_id = match rule with
    | Some r -> kw "rule" ^ r
    | None ->  ""
  in
  let html_of_section_kind_and_name (s, n) =
    span "lex-section-kind" (Lex.string_of_section_kind s) ^ n in
  a ("#" ^ section_id (fst (Label.reference_of_label l))) "lex-section-link"
    ("{ " ^ String.concat ~sep:" " (List.map ~f:html_of_section_kind_and_name rs) ^ rule_id ^ " }")

let html_of_ref ref_id r =
  div "lex-formula" (span "lex-subformula" ~id:(Some ref_id) (html_of_reference r))
  
let html_of_erule rule_id erule =
  let formula_id infix =
    Printf.sprintf "%s-%s-%d" rule_id infix in
  let string_of_imp_rule verb f p g q =
    div "lex-rule-if" (
        kw "whenever"
        ^ html_of_pattern "if-pattern" p
        ^ String.concat ~sep:"" (List.mapi ~f:(fun i f -> html_of_formula (formula_id "if" i) f) f)
      )
    ^ div "lex-rule-then" (
          kw verb
          ^ html_of_pattern "then-pattern" q
          ^ String.concat ~sep:"" (List.mapi ~f:(fun i f -> html_of_formula (formula_id "then" i) f) g)
        )
  in
  let string_of_ref_rule verb f p refs =
    div "lex-rule-if" (
        kw "whenever"
        ^ html_of_pattern "if-pattern" p
        ^ String.concat ~sep:"" (List.mapi ~f:(fun i f -> html_of_formula (formula_id "if" i) f) f)
      )
    ^ div "lex-rule-then" (
          kw verb
          ^ String.concat ~sep:"" (List.mapi ~f:(fun i r -> html_of_ref (formula_id "then" i) r) refs)
        )
  in
  match erule with
  | EObligation (f, p, g, q)
    | EPermission (f, p, g, q)
    -> string_of_imp_rule (verb_of_erule erule) (List.map ~f:snd f) p (List.map ~f:snd g) q
  | EConstitutive (f, p, g)
    -> string_of_imp_rule (verb_of_erule erule) (List.map ~f:snd f) p (List.map ~f:snd g) EPPresent
  | EException (f, p, refs, _)
  | EScope (f, p, refs, _)
    -> string_of_ref_rule (verb_of_erule erule) (List.map ~f:snd f) p (List.map ~f:(fun (_,l,x) -> (l, x)) refs)

let html_of_rule_type = function
  | Lex.Vanilla -> ""
  | Enforceable -> "enforceable"
  | Transparent -> "transparently enforceable"

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
      ident id ^ ": " ^ typ (Formula.TypeTerm.value_to_string ty)
    )

let html_of_function_arg (id, ty) =
  div "lex-function-arg" (
      ident id ^ ": " ^ typ (Formula.TypeTerm.value_to_string ty)
    )

let html_of_type_fix rule_id i (ident_, ty) =
  let id = Some (Printf.sprintf "%s-fix-%d" rule_id i) in
  div "lex-type-fix-outer" (
      span ~id "lex-type-fix" (ident ident_ ^ ": " ^ typ (Formula.TypeTerm.value_to_string ty))
    )

let html_of_args args =
  div "lex-event-args" (
      String.concat ~sep:"" (List.map ~f:html_of_arg args)
    )

let html_of_function_args args =
  div "lex-function-args" (
      String.concat ~sep:", " (List.map ~f:html_of_function_arg args)
    )

let html_of_type_fixes rule_id = function
  | [] -> ""
  | type_fixes -> 
     div "lex-type-fixes" (
         kw "fix" ^ String.concat ~sep:"" (List.mapi ~f:(html_of_type_fix rule_id) type_fixes)
       )

let html_of_label label =
  let html_of_label_reference rs =
    let html_of_section_kind_and_name rs' (s, n) =
      let rs' = rs' @ [(s, n)] in
      rs', a ("#" ^ section_id rs') "lex-section-link" (Lex.string_of_section_kind s ^ " " ^ n) in
    String.concat ~sep:" / " (snd (List.fold_map ~init:[] ~f:html_of_section_kind_and_name rs)) in
  let reference = Util.butlast (fst (Label.reference_of_label label)) in
  if List.is_empty reference then "" else span "lex-section-links" (html_of_label_reference reference)

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
  | ESSection (section_kind, label, name, title) ->
     let section_class = "lex-stmt-section-" ^ Lex.string_of_section_kind section_kind in
     let section_id = section_id (fst (Label.reference_of_label label)) in
     div ~id:(Some section_id) section_class (
         one_column ~title:true (
             span "lex-section-kind" (Lex.string_of_section_kind section_kind)
             ^ span "lex-section-label" name
             ^ html_of_label label
             ^ (
               match title with
               | Some title -> div "lex-section-title" (html_of_tannot title)
               | None -> ""
             )
           )
       )
  | ESRule (_, _, label, type_fixes, erule, rule_type, rule_constrs, doc_string) ->
    let rule_id = Label.qualified_id label in
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
          (html_of_erule_reading ("lex-subformula-reading-" ^ rule_id)
             eprog type_fixes erule doc_string)
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
     let html_of_type =
       typ name ^
         (match ty with Some tt -> kw "is" ^ typ (Dom.string_of_tt tt) | None -> "") in
     div "lex-stmt-type"
       (match doc_string with
        | Some s -> two_column html_of_type (html_of_doc_string s)
        | None   -> one_column html_of_type)
  | ESFunction (name, typed_args, return_type, doc_string) ->
     let html_of_function =
       ident name
       ^ html_of_function_args typed_args
       ^ " -> "
       ^ typ (Formula.TypeTerm.value_to_string return_type)
     in
     div "lex-stmt-function"
       (match doc_string with
        | Some s -> two_column html_of_function (html_of_doc_string s)
        | None   -> one_column html_of_function)
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
