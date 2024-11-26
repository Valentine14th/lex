open Core

open LegalXml

let debug_formex = ref false
let debug msg = if !debug_formex then Errors.debug_print ~f_name:(Some "formex.ml") msg

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
             map_data (fun s -> text ^ " [...] " ^ s) t
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

let read_file filepath filename =
  let fullname = Filename.concat filepath filename in
  let xml = XML.parse_file fullname in
  let title = get_law_title xml in
  let initial_node = make_empty_node (Lex.Law 0)
                       (Filename.chop_extension filename) (Some title) in
  let enacting_terms = get_enacting_terms xml in
  let node = fill_in enacting_terms initial_node in
  debug (to_string_structure node);
  node
  
(* Does not currently support levels above chapters  *)
