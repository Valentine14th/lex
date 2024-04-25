open Core
open Lex_lib

let loop filename mode o () =
  let lexpath = Filename.dirname (Sys.get_argv()).(0) in
  let filepath = Filename.dirname filename
  and basename = Filename.basename filename in

  match mode with
  | None | Some "mfotl" -> begin
      let eprog = Modules.do_type [lexpath] filepath basename  in
      Elex.print_eprog eprog;
      print_endline "#################\n";
      Compiler.compile eprog (* compile correctly typed program *)
    end
  | Some "doc" -> begin
      let eprog = Modules.do_type [lexpath] filepath basename  in
      let outname = Option.fold o ~init:(filename ^ "_doc.html") ~f:(fun _ x -> x) in
      Doc.to_file basename outname eprog
    end
  | Some "template" -> begin
      let formex = Formex.read_file filepath basename in
      let name = Filename.chop_extension basename in
      let lex = Formex.to_lex [name] formex in
      let outname = Option.fold o ~init:(filename ^ "_lex.lex") ~f:(fun _ x -> x) in
      Lex.prog_to_file outname lex
    end
  | Some _ -> assert false


let () =
  Command.basic_spec ~summary:"Parse Lex"
    Command.Spec.(empty
                  +> anon ("filename" %: string)
                  +> flag "-mode" (optional string) ~doc:"mode options: mfotl (default), doc, template"
                  +> flag "-o" (optional string) ~doc:"output file")
    loop
  |> Command_unix.run
     
