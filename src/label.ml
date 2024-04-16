open Core
open Lex
(* open Util *)

(** First identifier: number, letter, etc. describing
                      the section in question (e.g. "2")
    second identifier: decriptive, title (e.g. "Material Scope") *)
type label_levels = (ident * ident) list 

type t =
  {
    law: label_levels; (* for qualified name, this must be non-empty *)
    title: label_levels; (* ignored for qualified name *)
    chapter: label_levels; (* ignored for qualified name *)
    section: label_levels; (* ignored for qualified name *)
    article: label_levels; (* for qualified name, this must be non-empty *)
    paragraph: label_levels;
    point: label_levels;
    subpoint: label_levels
  }

let empty =
  {
    law = [];
    title = [];
    chapter = [];
    section = [];
    article = [];
    paragraph = [];
    point = [];
    subpoint = []
  }

let qualified_name_of_law pos = function
  | [] -> Util.label_error "No 'law' section defined (yet). A rule must be inside of a 'law' section" pos
  | (name, _) :: _ -> name


let rec qualified_name_of_level pos = function
  | [] -> ""
  (* | (name, _, _) :: xs -> "(" ^ name ^ ")" ^ qualified_name_of_level xs *)
  | (name, _) :: xs -> "(" ^ name ^ ")" ^ qualified_name_of_level pos xs

let qualified_name_of_article pos = function
  | [] -> Util.label_error "No 'article section defined (yet). A rule must be inside of a 'article' section" pos
  | (name, _) :: xs -> name ^ qualified_name_of_level pos xs

let qualified_name pos l =
  Printf.sprintf "%s %s%s%s%s"
  (qualified_name_of_law pos l.law)
  (qualified_name_of_article pos l.article)
  (qualified_name_of_level pos l.paragraph)
  (qualified_name_of_level pos l.point)
  (qualified_name_of_level pos l.subpoint)


let set pos section_kind label l =
  try
    match section_kind with
    (* | Law 0       -> { empty with law       = [label] } *)
    | Law i       -> {            law       = Util.take l.law i @ [label];       subpoint = []; point = []; paragraph = []; article = []; section = []; chapter = []; title = []}
    | Title i     -> { l     with title     = Util.take l.title i @ [label];     subpoint = []; point = []; paragraph = []; article = []; section = []; chapter = []}
    | Chapter i   -> { l     with chapter   = Util.take l.chapter i @ [label];   subpoint = []; point = []; paragraph = []; article = []; section = []}
    | Section i   -> { l     with section   = Util.take l.section i @ [label];   subpoint = []; point = []; paragraph = []; article = []}
    | Article i   -> { l     with article   = Util.take l.article i @ [label];   subpoint = []; point = []; paragraph = []}
    | Paragraph i -> { l     with paragraph = Util.take l.paragraph i @ [label]; subpoint = []; point = []}
    | Point i     -> { l     with point     = Util.take l.point i @ [label];     subpoint = []}
    | Subpoint i  -> { l     with subpoint  = Util.take l.subpoint i @ [label]}
  with
  | Invalid_argument _ -> Util.label_error ("wrong sub-level index (" ^ string_of_section_kind section_kind ^ ", " ^ qualified_name pos l ^ ")") pos

let collect l =
  let ls = [
    l.law;
    l.title;
    l.chapter;
    l.section;
    l.article;
    l.paragraph;
    l.point;
    l.subpoint
  ] in
  let is_empty = function
    | [] -> None
    | x -> Some x in
  List.filter_map ls ~f:is_empty



