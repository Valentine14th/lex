open Core


type t = { ident   : string;
           kind    : Lex.section_kind;
           title   : string option;
           children: node_t }

and node_t =
  | FormexNode of t list
  | FormexData of string

let make_empty_node kind ident title =
  { ident; kind; title; children = FormexNode [] }

let make_data node data =
  { node with children = FormexData data }

let rec to_string t =
  Printf.sprintf "[%s %s%s]: %s"
    (Lex.string_of_section_kind t.kind)
    t.ident
    (match t.title with None -> "" | Some t -> ": " ^ t)
    (to_string_node t.children)

and to_string_node = function
  | FormexNode ts -> "{" ^ String.concat (List.map ~f:to_string ts) ~sep:"; " ^ "}"
  | FormexData s -> s

(* XML *)

module XML = struct
  (* Issue: Xml-light does not support the dots in tag names used in Formex.
     Fix:   Remove the dots in all tag names using regular expressions. *)
  let tag_regex =
    Re.compile (Re.(alt [seq [char '<'; rep (compl [char '>']); char '>'];
                         seq [str "</"; rep (compl [char '>']); char '>']]))

  let dot_regex =
    Re.compile (Re.char '.')

  let parse_file filename =
    let contents = In_channel.read_all filename in
    let f group =
      let string = Re.Group.get group 0 in
      Re.replace dot_regex ~f:(fun _ -> "") string in
    let contents = Re.replace tag_regex ~f contents in
    Xml.parse_string contents

  let get_child_by_tag_name tag xml =
    List.find_exn ~f:(fun x -> String.equal (Xml.tag x) tag) (Xml.children xml)

  let find_childs_by_tag_name tag xml =
    List.filter ~f:(fun x -> String.equal (Xml.tag x) tag) (Xml.children xml)

  let rec text = function
    | Xml.PCData data -> data
    | Xml.Element (_, _, xmls) -> String.concat ~sep:" " (List.map ~f:String.strip (List.map ~f:text xmls))

end

(* End XML *)

let format_ident =
  Re.replace (Re.compile (Re.(alt [char '('; char ')'; char '.']))) ~f:(fun _ -> "")

let get_law_title xml =
  let title_xml = XML.get_child_by_tag_name "TITLE" xml in
  XML.text title_xml

let get_enacting_terms = XML.get_child_by_tag_name "ENACTINGTERMS"

let get_ident tag xml =
  let ti_xml = XML.get_child_by_tag_name tag xml in
  let text = XML.text ti_xml in
  format_ident (List.last_exn (String.split_on_chars text ~on:[' '; '\xa0']))

let get_idents tag = List.map ~f:(get_ident tag)

let get_title tag xml =
  let sti_xml = XML.get_child_by_tag_name tag xml in
  XML.text sti_xml

let get_titles tag = List.map ~f:(get_title tag)

let rec fill_in xml node =
  (*print_endline (String.sub (Xml.to_string xml) ~pos:0 ~len:64);
  print_endline (Lex.string_of_section_kind node.kind);*)
  match node.kind with
  | Lex.Law 0 -> fill_in_on_tag_name "DIVISION" (Some "TITLE") "TI" (Some "STI") (Lex.Chapter 0) xml node
  | Lex.Chapter 0 ->
     let section_xmls = XML.find_childs_by_tag_name "DIVISION" xml in
     begin
       if List.length section_xmls > 0 then
         fill_in_on_tag_name "DIVISION" (Some "TITLE") "TI" (Some "STI") (Lex.Section 0) xml node
       else
         fill_in_on_tag_name "ARTICLE" None "TIART" (Some "STIART") (Lex.Article 0) xml node
     end
  | Lex.Section 0 ->
     fill_in_on_tag_name "ARTICLE" None "TIART" (Some "STIART") (Lex.Article 0) xml node
  | Lex.Article 0 ->
     let paragraph_xmls = XML.find_childs_by_tag_name "PARAG" xml in
     let alinea_xmls = XML.find_childs_by_tag_name "ALINEA" xml in
     begin
       if List.length paragraph_xmls > 0 then
         fill_in_on_tag_name "PARAG" None "NOPARAG" None (Lex.Paragraph 0) xml node
       else if List.length alinea_xmls > 1 then
         fill_in_on_tag_name_implicit "ALINEA" (Lex.Point 0) xml node
       else if List.length alinea_xmls = 1 then
         fill_in_data "ALINEA" xml node
       else
         assert false (*no subdivision of article*)
     end
  | Lex.Paragraph 0 ->
     let alinea_xmls = XML.find_childs_by_tag_name "ALINEA" xml in
     begin
       if List.length alinea_xmls > 1 then
         fill_in_on_tag_name_implicit "ALINEA" (Lex.Point 0) xml node
       else if List.length alinea_xmls = 1 then
         fill_in_data "ALINEA" xml node
       else
         assert false
     end
  | _ -> assert false

and fill_in_on_tag_name tag tag_title' tag_ident tag_title kind xml node =
  let xmls = XML.find_childs_by_tag_name tag xml in
  let xmls' =
    match tag_title' with
    | Some tc -> List.map xmls ~f:(XML.get_child_by_tag_name tc)
    | None -> xmls in
  let idents = get_idents tag_ident xmls' in
  let titles = match tag_title with
    | Some tt -> List.map ~f:Option.return (get_titles tt xmls')
    | None -> List.init (List.length idents) ~f:(fun _ -> None) in
  let nodes = List.map2_exn ~f:(make_empty_node kind) idents titles in
  { node with children = FormexNode (List.map2_exn xmls nodes ~f:fill_in) }

and fill_in_on_tag_name_implicit tag kind xml node =
  let xmls = XML.find_childs_by_tag_name tag xml in
  let idents = List.init (List.length xmls) ~f:(fun i -> string_of_int (i+1)) in
  let titles = List.init (List.length xmls) ~f:(fun _ -> None) in
  let nodes = List.map2_exn ~f:(make_empty_node kind) idents titles in
  let texts = List.map xmls ~f:XML.text in
  { node with children = FormexNode (List.map2_exn nodes texts ~f:make_data) }

and fill_in_data tag xml node =
  let text = get_title tag xml in
  { node with children = FormexData text }

let to_module filepath filename =
  let fullname = Filename.concat filepath filename in
  let xml = XML.parse_file fullname in
  let title = get_law_title xml in
  let initial_node = make_empty_node (Lex.Law 0) (Filename.chop_extension filename) (Some title) in
  let enacting_terms = get_enacting_terms xml in
  fill_in enacting_terms initial_node



(* Does not currently support titles *)
(* Does not currently support lists *)
