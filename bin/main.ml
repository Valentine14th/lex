open Core
open Lex_lib

module Time = MFOTL_lib.Time

(* TODO: introduce the upper bound `b` as a command line paramter - analogous to WhyEnf *)
let loop filename mode f o b () =
  let lexpath = Filename.dirname (Sys.get_argv()).(0) in
  let filepath = Filename.dirname filename
  and basename = Filename.basename filename in
  let b = match b with (* TODO: does this way of extracting an upper bound b make sense? *)
    | None -> Time.Span.zero
    | Some b -> Time.Span.of_string b in

  match mode with
  | None | Some "mfotl" -> begin
      let eprog = Modules.do_type [lexpath] b filepath basename in
      (* Util.debug_print ~f_name:(Some "main.ml/loop") "Parsed and typed:\n"; *)
      (* if !Util.debug then Elex.print_eprog eprog; *)
      print_endline "Compiled:\n";
      let cprog = Compiler.compile eprog in
      print_endline (Clex.to_string cprog)
      (* compile correctly typed program *)
    end
  | Some "doc" -> begin
      let eprog = Modules.do_type [lexpath] b filepath basename in
      let outname = Option.fold o ~init:(filename ^ "_doc.html") ~f:(fun _ x -> x) in
      Doc.to_file basename outname eprog
    end
  | Some "template" -> begin
      let format, xml = match f with
        | Some "akomaNtoso" -> Lex.IAkomaNtoso, AkomaNtoso.read_file filepath basename
        | _ -> Lex.IFormex, Formex.read_file filepath basename in
      let name = Filename.chop_extension basename in
      let lex = LegalXml.to_lex format [name] xml in
      let outname = Option.fold o ~init:(filename ^ "_lex.lex") ~f:(fun _ x -> x) in
      Lex.prog_to_file outname lex
    end
  | Some _ -> assert false

let () =
  Command.basic_spec ~summary:"Parse Lex"
    Command.Spec.(empty
                  +> anon ("filename" %: string)
                  +> flag "-mode" (optional string) ~doc:"mode options: mfotl (default), doc, template"
                  +> flag "-f" (optional string) ~doc:"input format options: formex (default), akomaNtoso"
                  +> flag "-o" (optional string) ~doc:"output file"
                  +> flag "-b" (optional string) ~doc:"upper bound for the time interval"
                  )
    loop
  |> Command_unix.run
     
