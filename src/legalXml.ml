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
  ^ (match t.title with Some title -> ": " ^ title  | None -> "")
  ^ to_string_node_structure ~lvl t.children

and to_string_node_structure ?lvl:(lvl=0) = function
  | FormexNode ts -> String.concat ~sep:"" (List.map ts ~f:(fun t -> "\n" ^ to_string_structure ~lvl:(lvl+1) t))
  | FormexData _ -> ""

let rec find_data t filters =
  match t.children, filters with
  | FormexData s, [] -> Some s
  | FormexNode ts, (kind, ident) :: filters ->
     let matches t =
       Lex.equal_section_kind t.kind kind && String.equal t.ident ident in
     let f t =
       if matches t then
         find_data t filters
       else
         find_data t ((kind, ident) :: filters)
     in
     List.find_map ts ~f
  | _, _ -> None

let rec find_title t filters =
  match t.children, filters with
  | _, [] -> t.title
  | FormexNode ts, (kind, ident) :: filters ->
     let matches t =
       Lex.equal_section_kind t.kind kind && String.equal t.ident ident in
     let f t =
       if matches t then
         find_title t filters
       else
         find_title t ((kind, ident) :: filters)
     in
     List.find_map ts ~f
  | _, _ -> None

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

  let has_child_by_tag_name tag xml =
    List.exists ~f:(fun x -> String.equal (Xml.tag x) tag) (Xml.children xml)

  let get_child_by_tag_name tag xml =
    List.find_exn ~f:(fun x -> String.equal (Xml.tag x) tag) (Xml.children xml)

  let find_children_by_tag_name tag xml =
    try
      List.filter ~f:(fun x -> String.equal (Xml.tag x) tag) (Xml.children xml)
    with Xml.Not_element _ -> []

  let attr key = function
    | Xml.PCData _ -> assert false
    | Xml.Element (_, attrs, _) ->
       List.find_map_exn attrs
         ~f:(fun (key', value) -> if String.equal key key' then Some value else None)

  let rec text = function
    | Xml.PCData data -> String.strip data
    | Xml.Element (_, _, xmls) -> String.strip (String.concat ~sep:" " (List.map ~f:String.strip (List.map ~f:text xmls)))

  let tag = Xml.tag

end

(* End XML *)

let rec to_lex_sections t =
  Lex.SSection (LexingInfo.dummy, t.kind, t.ident, None) :: to_lex_node_sections t.children

and to_lex_node_sections = function
  | FormexNode ts -> List.concat_map ts ~f:to_lex_sections
  | FormexData s -> [Lex.SNote (LexingInfo.dummy, s)]

let to_lex format name t =
  let sections = to_lex_sections t in
  let stmts = (Lex.SImport (LexingInfo.dummy, format, name)) :: sections in
  Lex.{stmts}
    
