open Core
open Lexing

type t =
  | MLex of Elex.eprog
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

let link_formex_stmt modules = function
  | Tlex.TSRule (_, _, _, _, _, Some _) as s -> s
  | TSSection (section_kind, full_label, label, None) ->
     let law = Label.qualified_name_of_law full_label.law in
     let title = begin
         print_endline (String.concat ~sep:" " (
                            List.map (Label.full_filters full_label)
                              ~f:(fun (kind, ident) -> Lex.string_of_section_kind kind ^ " " ^ ident)));
         match Map.find modules law with
         | Some (MFormex formex) ->
            Option.map (Formex.find_title formex (List.tl_exn (Label.full_filters full_label)))
              ~f:(fun x -> Tlex.TAFormex (law, x))
         | _ -> None
       end 
     in TSSection (section_kind, full_label, label, title)
  | TSRule (pos, label, rule, rule_type, rule_constrs, None) ->
     let law = Label.qualified_name_of_law label.law in
     let doc_string = begin
         match Map.find modules law with
         | Some (MFormex formex) ->
            Option.map (Formex.find_data formex (List.tl_exn (Label.full_filters label)))
              ~f:(fun x -> Tlex.TAFormex (law, x))
         | _ -> None
       end 
     in TSRule (pos, label, rule, rule_type, rule_constrs, doc_string)
  | s -> s

let link_formex modules tprog =
  Tlex.{ tprog with tstmts = List.map tprog.tstmts ~f:(link_formex_stmt modules) }

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
                          | SIFormex _ -> MFormex (Formex.read_file filepath' filename'))
                       )
                      )
                    ) in
  let modules = Map.of_alist_exn (module String) modules in
  let tprog = Typing.do_type modules prog in
  let tprog = link_formex modules tprog in
  let eprog = Enforceability.do_type modules tprog in 
  eprog

