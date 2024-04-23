open Core
open Lex_lib

let loop filename mode () =
  let lexpath = Filename.dirname (Sys.get_argv()).(0) in
  let filepath = Filename.dirname filename
    and filename = Filename.basename filename in
  let eprog = Modules.do_type [lexpath] filepath filename  in
  match mode with
  | None | Some "mfotl" -> begin
      Elex.print_eprog eprog;
      print_endline "#################\n";
      Compiler.compile eprog; (* compile correctly typed program *)
    end
  | Some "doc" -> begin
      Doc.print filename (filename ^ "_doc.html") eprog
    end
  | Some _ -> assert false


let () =
  Command.basic_spec ~summary:"Parse Lex"
    Command.Spec.(empty
                  +> anon ("filename" %: string)
                  +> flag "-mode" (optional string) ~doc:"mode options: mfotl (default), doc")
    loop
  |> Command_unix.run
     
