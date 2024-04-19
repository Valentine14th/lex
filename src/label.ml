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
    subpoint: label_levels;
    rule_id: string option
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
    subpoint = [];
    rule_id = None
  }

let valid_rule_label pos = function
  | { law = []; _ } -> Util.label_error "No 'law' section defined (yet). A rule must be inside of a 'law' section" pos
  | { article = []; _ } -> Util.label_error "No 'article section defined (yet). A rule must be inside of an 'article' section" pos
  | _ -> ()

let qualified_name_of_law = function
  | [] -> ""
  | (name, _) :: _ -> name ^ " "


let rec qualified_name_of_level = function
  | [] -> ""
  | (name, _) :: xs -> "(" ^ name ^ ")" ^ qualified_name_of_level xs

let qualified_name_of_article = function
  | [] -> ""
  | (name, _) :: xs -> name ^ qualified_name_of_level xs

let string_of_rule_id = function
  | None -> ""
  | Some s -> "#" ^ s

let qualified_name l =
  Printf.sprintf "%s%s%s%s%s%s"
  (qualified_name_of_law l.law)
  (qualified_name_of_article l.article)
  (qualified_name_of_level l.paragraph)
  (qualified_name_of_level l.point)
  (qualified_name_of_level l.subpoint)
  (string_of_rule_id l.rule_id)


let set pos section_kind label l =
  try
    match section_kind with
    | Law i       -> {            law       = Util.take l.law i @ [label];       rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []; chapter = []; title = []}
    | Title i     -> { l     with title     = Util.take l.title i @ [label];     rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []; chapter = []}
    | Chapter i   -> { l     with chapter   = Util.take l.chapter i @ [label];   rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []}
    | Section i   -> { l     with section   = Util.take l.section i @ [label];   rule_id = None; subpoint = []; point = []; paragraph = []; article = []}
    | Article i   -> { l     with article   = Util.take l.article i @ [label];   rule_id = None; subpoint = []; point = []; paragraph = []}
    | Paragraph i -> { l     with paragraph = Util.take l.paragraph i @ [label]; rule_id = None; subpoint = []; point = []}
    | Point i     -> { l     with point     = Util.take l.point i @ [label];     rule_id = None; subpoint = []}
    | Subpoint i  -> { l     with subpoint  = Util.take l.subpoint i @ [label];  rule_id = None;}
  with
  | Invalid_argument _ -> Util.label_error ("wrong sub-level index (" ^ string_of_section_kind section_kind ^ ", " ^ qualified_name l ^ ")") pos

let set_rule_id rule_id l = { l with rule_id = rule_id }

(* IDEA: remove the lowest level from the label
         while ignoring label parts that are not
         used for qualified names *)
let scope l = match l.rule_id with
  | Some _ -> { l with rule_id = None }
  | None -> begin match List.rev l.subpoint with
    | _::xs -> { l with subpoint = List.rev xs }
    | [] -> begin match List.rev l.point with
      | _::xs -> { l with point = List.rev xs }
      | [] -> begin match List.rev l.paragraph with
        | _::xs -> { l with paragraph = List.rev xs }
        | [] -> begin match List.rev l.article with
          | _::xs -> { l with article = List.rev xs }
          | [] -> empty
        end
      end
    end
  end

let rec prefixes l = match scope l with
  | { law = []; title = _; chapter = _; section = _; article = []; paragraph = []; point = []; subpoint = []; rule_id = None } -> [empty]
  | l' -> l' :: prefixes l'

