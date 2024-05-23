open Core

let class_list = [
    ("lex-program", "lex-program col-12");
    ("lex-stmt-import", "lex-stmt lex-stmt-import");
    ("lex-stmt-type", "lex-stmt lex-stmt-type");
    ("lex-stmt-event", "lex-stmt lex-stmt-event");
    ("lex-stmt-rule", "lex-stmt lex-stmt-rule");
    ("lex-stmt-note", "lex-stmt lex-stmt-note");
    ("lex-event-reading", "lex-reading card");
    ("lex-rule-reading", "lex-reading card");
    ("lex-reading-header", "card-header");
    ("lex-reading-body", "card-body");
    ("lex-stmt-section-law", "lex-stmt-section lex-stmt-section-law");
    ("lex-stmt-section-title", "lex-stmt-section lex-stmt-section-title");
    ("lex-stmt-section-chapter", "lex-stmt-section lex-stmt-section-chapter");
    ("lex-stmt-section-section", "lex-stmt-section lex-stmt-section-section");
    ("lex-stmt-section-article", "lex-stmt-section lex-stmt-section-article");
    ("lex-stmt-section-paragraph", "lex-stmt-section lex-stmt-section-paragraph");
    ("lex-stmt-section-point", "lex-stmt-section lex-stmt-section-point");
    ("lex-stmt-section-subpoint", "lex-stmt-section lex-stmt-section-subpoint");
  ]


let class_map = Map.of_alist_exn (module String) class_list

let classes class_ = match Map.find class_map class_ with
  | Some c -> c
  | None -> class_

let id_html id = match id with
  | None -> ""
  | Some i -> " id=\"" ^ i ^ "\""

let tag name ?id:(id=None) class_ html =
  Printf.sprintf "<%s class=\"%s\"%s>%s</%s>"
    name (classes class_) (id_html id) html name

let a ?id:(id=None) href class_ html =
  Printf.sprintf "<a href=\"%s\" class=\"%s\"%s>%s</a>"
    href (classes class_) (id_html id) html 

let span ?id:(id=None) = tag "span" ~id 

let div ?id:(id=None) = tag "div" ~id

let p = tag "p"

let ul = tag "ul"

let li = tag "li"

let strong = tag "strong"

let interval html =
  if String.equal html "" then
    ""
  else
    span "lex-interval" html

let kw html =
  span "lex-keyword" html

let const html =
  span "lex-const" html

let ident html =
  span "lex-ident" html

let typ html =
  span "lex-typ" html

let string html =
  kw "\"" ^ span "lex-string" html ^ kw "\""

let two_column left right =
  div "row" (div "col-6" left ^ div "col-6" right)

let one_column ?(title=false) html =
  if title then
    div "row title-row" (div "col-12" html)
  else
    div "row" (div "col-12" html)

let badge html =
  span "badge" html

let formex html =
  badge ("XML: " ^ html)
