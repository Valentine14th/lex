open Core

type t = int

(* Issue: Xml-light does not support the dots in tag names used in Formex.
   Fix:   Remove the dots in all tag names using regular expressions. *)
let tag_regex =
  Re.compile (Re.(alt [seq [char '<'; rep (alt [alpha; char '.']); char '>'];
                       seq [str "</"; rep (alt [alpha; char '.']); char '>']]))

let dot_regex =
  Re.compile (Re.char '.')

let parse_file filename =
  let contents = In_channel.read_all filename in
  let f group =
    let string = Re.Group.get group 0 in
    Re.replace dot_regex ~f:(fun _ -> "") string in
  let contents = Re.replace tag_regex ~f contents in
  Xml.parse_file contents
  
let to_module filepath filename =
  let fullname = Filename.concat filepath filename in
  let xml = Xml.parse_file fullname in
  print_endline (Xml.tag xml);
  0

