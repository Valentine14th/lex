open Core

open LegalXml

let debug_akomaNtoso = ref false
let debug msg = if !debug_akomaNtoso then Util.debug_print ~f_name:(Some "akomaNtoso.ml") msg else ignore msg

let format_ident =
  Re.replace (Re.compile (Re.(alt [char '('; char ')'; char '.']))) ~f:(fun _ -> "")

let get_act = XML.get_child_by_tag_name "act"
  
let get_law_title xml =
  let act_xml = get_act xml in
  let preface_xml = XML.get_child_by_tag_name "preface" act_xml in
  let ps_xml = XML.find_children_by_tag_name "p" preface_xml in
  let p_xml = List.find_exn ps_xml ~f:(XML.has_child_by_tag_name "docTitle") in
  let title_xml = XML.get_child_by_tag_name "docTitle" p_xml in
  XML.text title_xml

let get_body xml =
  let act_xml = get_act xml in
  XML.get_child_by_tag_name "body" act_xml

let get_ident xml =
  let eId = XML.attr "eId" xml in
  if StringLabels.ends_with ~suffix:"para" eId then
    "1"
  else
    format_ident (List.last_exn (String.split_on_chars eId ~on:['_']))

let get_idents = List.map ~f:get_ident

let get_text tag xml =
  try let sti_xml = XML.get_child_by_tag_name tag xml in
      XML.text sti_xml
  with Not_found_s _ -> ""

let get_texts tag = List.map ~f:(get_text tag)

let rec fill_in xml node =
  debug (to_string node);
  let fill_in_points xml node kind =
    let list_xml = XML.get_child_by_tag_name "blockList" xml in
    let text = get_text "listIntroduction" list_xml in
    try
      let t = fill_in_on_tag_name "item" None
                None kind list_xml node in
      map_data (fun s -> text ^ " [...] " ^ s) t
    with _ -> fill_in_data_self xml node
  in
  match node.kind with
  | Lex.Law 0 ->
     fill_in_on_tag_name "chapter" None (Some "heading") (Lex.Chapter 0) xml node
  | Lex.Chapter 0 ->
     let section_xmls = XML.find_children_by_tag_name "section" xml in
     begin
       if List.length section_xmls > 0 then
         fill_in_on_tag_name "section" None (Some "heading") (Lex.Section 0) xml node
       else
         fill_in_on_tag_name "article" None (Some "heading") (Lex.Article 0) xml node
     end
  | Lex.Section 0 ->
     fill_in_on_tag_name "article" None (Some "heading") (Lex.Article 0) xml node
  | Lex.Article 0 ->
     let paragraph_xmls = XML.find_children_by_tag_name "paragraph" xml in
     begin
       if List.length paragraph_xmls > 0 then
         fill_in_on_tag_name "paragraph" (Some "content") None (Lex.Paragraph 0) xml node
       else
         node
     end
  | Lex.Paragraph 0 ->
     let list_xmls = XML.find_children_by_tag_name "blockList" xml in
     begin
       if List.length list_xmls = 1 then
         fill_in_points xml node (Lex.Point 0)
       else if List.length list_xmls = 0 then
         fill_in_data_self xml node
       else
         assert false
     end
  | Lex.Point 0 ->
     let list_xmls = XML.find_children_by_tag_name "blockList" xml in
     begin
       if List.length list_xmls = 1 then
         fill_in_points xml node (Lex.Subpoint 0)
       else if List.length list_xmls = 0 then
         fill_in_data_self xml node
       else
         assert false
     end
  | Lex.Subpoint 0 -> fill_in_data_self xml node
  | _ -> assert false

and fill_in_on_tag_name tag tag_content tag_title kind xml node =
  let xmls = XML.find_children_by_tag_name tag xml in
  let xmls' =
    match tag_content with
    | Some tc -> List.map xmls ~f:(XML.get_child_by_tag_name tc)
    | None -> xmls in
  let idents = get_idents xmls in
  let titles = match tag_title with
    | Some tt -> List.map ~f:Option.return (get_texts tt xmls)
    | None -> List.init (List.length idents) ~f:(fun _ -> None) in
  let nodes = List.map2_exn ~f:(make_empty_node kind) idents titles in
  { node with children = FormexNode (List.map2_exn xmls' nodes ~f:fill_in) }

and fill_in_data tag xml node =
  let text = get_text tag xml in
  { node with children = FormexData text }

and fill_in_data_self xml node =
  { node with children = FormexData (XML.text xml) }

let read_file filepath filename =
  let fullname = Filename.concat filepath filename in
  let xml = XML.parse_file fullname in
  let title = get_law_title xml in
  let initial_node = make_empty_node (Lex.Law 0)
                       (Filename.chop_extension filename) (Some title) in
  let body = get_body xml in
  let node = fill_in body initial_node in
  debug (to_string node);
  node    

(* Does not currently support levels above chapters  *)
