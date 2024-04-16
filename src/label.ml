open Core
open Lex
(* open Util *)

(** First identifier: number, letter, etc. describing
                      the section in question
    second identifier: optional, decriptive, title *)
type label_levels = (ident * ident option) list

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

let set section_kind label l =
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

(* let collect_qualified_names l =
  let ls = [
    l.law;
    l.article;
    l.paragraph;
    l.point;
    l.subpoint
  ] in
  List.filter_map ls ~f:(fun x -> x) *)


(* let string_of_law (name, _, sub_levels) = name (* TODO: decide if ignoring sub levels on the title level is okay for the qualified name *) *)
let qualified_name_of_law = function
  | [] -> assert false (* TODO: throw proper error message *)
  | (name, _) :: _ -> name

let rec qualified_name_of_level = function
  | [] -> ""
  (* | (name, _, _) :: xs -> "(" ^ name ^ ")" ^ qualified_name_of_level xs *)
  | (name, _) :: xs -> "(" ^ name ^ ")" ^ qualified_name_of_level xs

let qualified_name l =
  Printf.sprintf "%s %s%s%s%s"
  (qualified_name_of_law l.law)
  (qualified_name_of_level l.article)
  (qualified_name_of_level l.paragraph)
  (qualified_name_of_level l.point)
  (qualified_name_of_level l.subpoint)



