open Core

let class_list = [
    ("lex-program", "lex-program col-12");
    ("lex-stmt-import", "lex-stmt lex-stmt-import");
    ("lex-stmt-type", "lex-stmt lex-stmt-type");
    ("lex-stmt-event", "lex-stmt lex-stmt-event");
    ("lex-stmt-rule", "lex-stmt lex-stmt-rule");
    ("lex-event-reading", "lex-reading card");
    ("lex-rule-reading", "lex-reading card");
    ("lex-reading-header", "card-header");
    ("lex-reading-body", "card-body");
    ("lex-stmt-section-law", "lex-stmt-section lex-stmt-section-law");
  ]


let class_map = Map.of_alist_exn (module String) class_list

let tag name class_ html =
  let classes = match Map.find class_map class_ with
    | Some c -> c
    | None -> class_ in
  Printf.sprintf "<%s class=\"%s\">%s</%s>" name classes html name

let span = tag "span" 

let div = tag "div"

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

let two_column left right =
  div "row" (div "col-6" left ^ div "col-6" right)

let one_column html =
  div "row" (div "col-12" html)

let badge html =
  span "badge" html

let formex html =
  badge ("Formex: " ^ html)
