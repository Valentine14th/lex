open Core


type t = { ident   : string;
           kind    : Lex.section_kind;
           title   : string option;
           children: node_t }

and node_t =
  | FormexNode of t list
  | FormexData of string

let rec map_data f t =
  { t with children = map_node_data f t.children }
and map_node_data f = function
  | FormexNode ts -> FormexNode (List.map ts ~f:(map_data f))
  | FormexData s -> FormexData (f s)

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

let rec to_string_structure ?lvl:(lvl=0) t =
  Util.spaces lvl ^ Lex.string_of_section_kind t.kind ^ " " ^ t.ident
  ^ to_string_node_structure ~lvl t.children

and to_string_node_structure ?lvl:(lvl=0) = function
  | FormexNode ts -> String.concat ~sep:"" (List.map ts ~f:(fun t -> "\n" ^ to_string_structure ~lvl:(lvl+1) t))
  | FormexData _ -> ""
  

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

  let find_children_by_tag_name tag xml =
    try
      List.filter ~f:(fun x -> String.equal (Xml.tag x) tag) (Xml.children xml)
    with Xml.Not_element _ -> []

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

let get_text tag xml =
  let sti_xml = XML.get_child_by_tag_name tag xml in
  XML.text sti_xml

let get_texts tag = List.map ~f:(get_text tag)

let rec fill_in xml node =
  let fill_in_point xml node kind =
    let list_xmls = XML.find_children_by_tag_name "LIST" xml in
     begin
       if List.length list_xmls > 0 then
         begin
           let list_xml = XML.get_child_by_tag_name "LIST" xml in
           let text = get_text "P" xml in
           try
             let t = fill_in_on_tag_name "ITEM" (Some "NP") "NOP"
                       None kind list_xml node in
             map_data (fun s -> text ^ "... " ^ s) t
           with _ -> fill_in_data_self xml node
         end
       else
         fill_in_data_self xml node
     end
  in
  match node.kind with
  | Lex.Law 0 ->
     fill_in_on_tag_name "DIVISION" (Some "TITLE") "TI" (Some "STI") (Lex.Chapter 0) xml node
  | Lex.Chapter 0 ->
     let section_xmls = XML.find_children_by_tag_name "DIVISION" xml in
     begin
       if List.length section_xmls > 0 then
         fill_in_on_tag_name "DIVISION" (Some "TITLE") "TI" (Some "STI") (Lex.Section 0) xml node
       else
         fill_in_on_tag_name "ARTICLE" None "TIART" (Some "STIART") (Lex.Article 0) xml node
     end
  | Lex.Section 0 ->
     fill_in_on_tag_name "ARTICLE" None "TIART" (Some "STIART") (Lex.Article 0) xml node
  | Lex.Article 0 ->
     let paragraph_xmls = XML.find_children_by_tag_name "PARAG" xml in
     let alinea_xmls = XML.find_children_by_tag_name "ALINEA" xml in
     begin
       if List.length paragraph_xmls > 0 then
         fill_in_on_tag_name "PARAG" None "NOPARAG" None (Lex.Paragraph 0) xml node
       else if List.length alinea_xmls > 0 then
         fill_in_on_tag_name_implicit "ALINEA" (Lex.Point 0) xml node
       else
         assert false
     end
  | Lex.Paragraph 0 ->
     let alinea_xmls = XML.find_children_by_tag_name "ALINEA" xml in
     begin
       if List.length alinea_xmls > 1 then
         fill_in_on_tag_name_implicit "ALINEA" (Lex.Point 0) xml node
       else if List.length alinea_xmls = 1 then
         fill_in_point (XML.get_child_by_tag_name "ALINEA" xml) node (Lex.Point 0)
       else
         assert false
     end
  | Lex.Point 0 -> fill_in_point xml node (Lex.Subpoint 0)
  | Lex.Subpoint 0 -> fill_in_data_self xml node
  | _ -> assert false

and fill_in_on_tag_name tag tag_title' tag_ident tag_title kind xml node =
  let xmls = XML.find_children_by_tag_name tag xml in
  let xmls' =
    match tag_title' with
    | Some tc -> List.map xmls ~f:(XML.get_child_by_tag_name tc)
    | None -> xmls in
  let idents = get_idents tag_ident xmls' in
  let titles = match tag_title with
    | Some tt -> List.map ~f:Option.return (get_texts tt xmls')
    | None -> List.init (List.length idents) ~f:(fun _ -> None) in
  let nodes = List.map2_exn ~f:(make_empty_node kind) idents titles in
  { node with children = FormexNode (List.map2_exn xmls nodes ~f:fill_in) }

and fill_in_on_tag_name_implicit tag kind xml node =
  let xmls = XML.find_children_by_tag_name tag xml in
  let idents = List.init (List.length xmls) ~f:(fun i -> string_of_int (i+1)) in
  let titles = List.init (List.length xmls) ~f:(fun _ -> None) in
  let nodes = List.map2_exn ~f:(make_empty_node kind) idents titles in
  { node with children = FormexNode (List.map2_exn xmls nodes ~f:fill_in) }

and fill_in_data tag xml node =
  let text = get_text tag xml in
  { node with children = FormexData text }

and fill_in_data_self xml node =
  { node with children = FormexData (XML.text xml) }

let to_module filepath filename =
  let fullname = Filename.concat filepath filename in
  let xml = XML.parse_file fullname in
  let title = get_law_title xml in
  let initial_node = make_empty_node (Lex.Law 0)
                       (Filename.chop_extension filename) (Some title) in
  let enacting_terms = get_enacting_terms xml in
  let node = fill_in enacting_terms initial_node in
  (*print_endline (to_string_structure node);*)
  node


(* Does not currently support levels above chapters  *)
