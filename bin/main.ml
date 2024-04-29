open Core
open Lex_lib

let loop filename mode label f o () =
  let lexpath = Filename.dirname (Sys.get_argv()).(0) in
  let filepath = Filename.dirname filename
  and basename = Filename.basename filename in

  let labelconvention = match label with
    | None | Some "standard" -> (module Label.StandardConvention : Label.LabelConvention)
    | Some _ -> assert false in

  match mode with
  | None | Some "mfotl" -> begin
      let eprog = Modules.do_type [lexpath] filepath basename labelconvention in
      Elex.print_eprog eprog;
      print_endline "#################\n";
      Compiler.compile eprog (* compile correctly typed program *)
    end
  | Some "doc" -> begin
      let eprog = Modules.do_type [lexpath] filepath basename labelconvention in
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
                  +> flag "-label" (optional string) ~doc:"label conventions: standard (default)"
                  +> flag "-f" (optional string) ~doc:"input format options: formex (default), akomaNtoso"
                  +> flag "-o" (optional string) ~doc:"output file")
    loop
  |> Command_unix.run
     
