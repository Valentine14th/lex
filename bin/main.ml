open Core
open Lex_lib

module Time = MFOTL_lib.Time

(* TODO: introduce the upper bound `b` as a command line paramter - analogous to WhyEnf *)
let loop filename mode f o b () =
  let open Errors.OrErrors in
  let lexpath = Filename.dirname (Sys.get_argv()).(0) in
  let filepath = Filename.dirname filename
  and basename = Filename.basename filename in
  let b = match b with (* TODO: does this way of extracting an upper bound b make sense? *)
    | None -> Time.Span.zero
    | Some b -> Time.Span.of_string b in

  match mode with
  | None | Some "mfotl" -> begin
      match Modules.do_type [lexpath] b filepath basename with
      | Ok (_, eprog) ->
         let cprog = Compiler.compile eprog in
         begin match o with
         | None -> print_endline (Clex.to_string cprog)
         | Some out_fn -> let sig_fn = out_fn ^ ".sig" in
                          let formula_fn = out_fn ^ ".mfotl" in
                          Clex.to_files cprog sig_fn formula_fn
         end
      | Errors errs ->
         print_string (Errors.to_string_multiple errs);
         exit (-1)
    end
  | Some "doc" -> begin
      match Modules.do_type [lexpath] b filepath basename with
      | Ok (_, eprog) -> 
         let outname = Option.fold o ~init:(filename ^ "_doc.html") ~f:(fun _ x -> x) in
         Doc.to_file basename outname eprog
      | Errors errs ->
         print_string (Errors.to_string_multiple errs);
         exit (-1)
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
     
