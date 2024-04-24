open Core
open Lex
(* open Util *)

(** First identifier: number, letter, etc. describing
                      the section in question (e.g. "2")
    second identifier: descriptive, title (e.g. "Material Scope") *)
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
    subpoint: label_levels;
    rule_id: ident option
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
  | (name, _) :: _ -> name

let qualified_filters_of_law = function
  | [] -> []
  | (name, _) :: _ -> [(Law 0, name)]

let rec qualified_name_of_level = function
  | [] -> ""
  | (name, _) :: xs -> "(" ^ name ^ ")" ^ qualified_name_of_level xs

let qualified_name_of_level_simple xs = String.concat ~sep:"_" (List.map ~f:fst xs)

let qualified_filters_of_level kind_fun xs =
  List.mapi xs ~f:(fun i (name, _) -> (kind_fun i, name))

let qualified_name_of_article = function
  | [] -> ""
  | (name, _) :: xs -> name ^ qualified_name_of_level xs

let string_of_rule_id = function
  | None -> ""
  | Some s -> "#" ^ s

let qualified_name l = match
  Printf.sprintf "%s %s%s%s%s%s"
  (qualified_name_of_law l.law)
  (qualified_name_of_article l.article)
  (qualified_name_of_level l.paragraph)
  (qualified_name_of_level l.point)
  (qualified_name_of_level l.subpoint)
  (string_of_rule_id l.rule_id)
  with
  | " " -> ""
  | s -> s

let qualified_id l =
  Printf.sprintf "%s-%s-%s-%s-%s-%s"
  (qualified_name_of_law l.law)
  (qualified_name_of_article l.article)
  (qualified_name_of_level_simple l.paragraph)
  (qualified_name_of_level_simple l.point)
  (qualified_name_of_level_simple l.subpoint)
  (string_of_rule_id l.rule_id)

let qualified_filters l =
  (qualified_filters_of_law l.law)
  @ (qualified_filters_of_level (fun i -> Article i) l.article)
  @ (qualified_filters_of_level (fun i -> Paragraph i) l.paragraph)
  @ (qualified_filters_of_level (fun i -> Point i) l.point)
  @ (qualified_filters_of_level (fun i -> Subpoint i) l.subpoint)

let full_filters l =
  (qualified_filters_of_law l.law)
  @ (qualified_filters_of_level (fun i -> Title i) l.title)
  @ (qualified_filters_of_level (fun i -> Chapter i) l.chapter)
  @ (qualified_filters_of_level (fun i -> Section i) l.section)
  @ (qualified_filters_of_level (fun i -> Article i) l.article)
  @ (qualified_filters_of_level (fun i -> Paragraph i) l.paragraph)
  @ (qualified_filters_of_level (fun i -> Point i) l.point)
  @ (qualified_filters_of_level (fun i -> Subpoint i) l.subpoint)

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
          (* | [] -> begin match List.rev l.law with
            | law::_ -> { l with law = [law] }
            | [] -> empty
          end *)
        end
      end
    end
  end

let rec prefixes l = match scope l with
  | { law = []; title = _; chapter = _; section = _; article = []; paragraph = []; point = []; subpoint = []; rule_id = None } -> [empty]
  | l' -> l' :: prefixes l'

let combine_prefix_with_exception_ident ident prefix = qualified_name prefix ^ ident

(** matches a partial name `ident` (used in exception) 
    inside a rule at position `pos` with the label `label`
    and returns the rule_id for which the exception is an 
    exception of*)
let get_full_name ident label pos rule_labels=
  let possible_names = List.map (prefixes label) ~f:(combine_prefix_with_exception_ident ident) in
  let actual_names = List.filter possible_names ~f:(fun n -> Map.mem rule_labels n) in
  let name = match actual_names with
  | [name] -> name
  | [] ->
    let err_msg = Printf.sprintf "Exception identifier '%s' could not be matched to a rule \n\tknown rules:          %s\n\tpotential expansions: %s"
                  (ident)
                  (Util.str_of_list (Map.keys rule_labels))
                  (Util.str_of_list possible_names)
    in
    Util.label_error err_msg pos
  | names ->
    let err_msg = Printf.sprintf "Exception identifier '%s' is ambiguous, could refer to multiple rules: %s"
                  (ident)
                  (Util.str_of_list names)
    in
    Util.label_error err_msg pos
  in
  let exception_name = qualified_name label in
  if String.equal exception_name name then
      let err_msg = Printf.sprintf "Exception rule '%s' cannot be an exception to itself ('%s')"
                    exception_name
                    name
      in
      Util.label_error err_msg pos
  else name
