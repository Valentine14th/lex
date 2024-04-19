open Core
open Lexing

type t =
  | MLex of Tlex.tprog
  | MFormex of Formex.t

type import =
  | SILex    of Lexing.position * string list
  | SIFormex of Lexing.position * string list

let string_of_import = function
  | SILex (_, idents) -> String.concat ~sep:"." idents
  | SIFormex (_, idents) -> String.concat ~sep:"." idents

let pos_of_import = function
  | SILex (pos, _) -> pos
  | SIFormex (pos, _) -> pos

let idents_of_import = function
  | SILex (_, idents) -> idents
  | SIFormex (_, idents) -> idents

let extension_of_import = function
  | SILex _ -> ".lex"
  | SIFormex _ -> ".xml"

let concat_all = function
  | [] -> ""
  | init::idents -> List.fold_left idents ~init ~f:Filename.concat 

let list_imports prog =
  let f = function
    | Lex.SImport (pos, ILex, idents)    -> Some (SILex (pos, idents))
    | Lex.SImport (pos, IFormex, idents) -> Some (SIFormex (pos, idents))
    | _ -> None
  in List.filter_map ~f Lex.(prog.stmts)

let suffix_of_import import =
  concat_all (idents_of_import import) ^ extension_of_import import

let check_filename (prefix, filename) =
  Sys_unix.is_file_exn ~follow_symlinks:false (Filename.concat prefix filename)

let find_filename seq import prefixes suffix =
  let candidates = List.map prefixes ~f:(fun prefix -> (prefix, suffix)) in
  match List.find candidates ~f:check_filename with
  | Some (prefix, filename) ->
     (if List.mem seq (Filename.concat prefix filename) ~equal:String.equal then
        Util.import_error
          (sprintf "found cyclic dependency %s"
             (String.concat ~sep:" -> " (seq @ [Filename.concat prefix filename])))
          (pos_of_import import)
      else
        (prefix, filename))
  | None -> Util.import_error
              (sprintf "cannot find file for importing %s"
                 (string_of_import import))
              (pos_of_import import)


let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s\n" (Util.string_of_pos pos)

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
    eprintf "%a: %s\n" print_position lexbuf msg;
    exit (-1)
  | Parser.Error ->
    eprintf "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let parse_module filename =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let prog = parse_with_error lexbuf in
  In_channel.close inx;
  prog

let rec do_type lexpath ?seq:(seq=[]) filepath filename =
  let fullname  = Filename.concat filepath filename in
  let seq'      = seq @ [fullname] in
  let prog      = parse_module fullname in
  let imports   = list_imports prog in
  let prefixes  = filepath :: lexpath in
  let suffixes  = List.map imports ~f:suffix_of_import in
  let filenames = List.map (List.zip_exn imports suffixes)
                    ~f:(fun (import, suffix) -> find_filename seq' import prefixes suffix) in
  let modules   = List.map (List.zip_exn filenames imports)
                    ~f:(fun ((filepath', filename'), import) ->
                      (let import_string = string_of_import import in
                       (
                         import_string,
                         (match import with
                          | SILex _    -> MLex (do_type lexpath ~seq:seq' filepath' filename')
                          | SIFormex _ -> MFormex (Formex.to_module filepath' filename'))
                       )
                      )
                    ) in
  Typing.do_type (Map.of_alist_exn (module String) modules) prog
