open Core
open Lexing

let debug_modules = ref false
let debug msg = if !debug_modules then Errors.debug_print ~f_name:(Some "modules.ml") msg

type t =
  | MLex of Elex.eprog
  | MLegalXml of LegalXml.t

type import =
  | SILex        of LexingInfo.t * string list
  | SIFormex     of LexingInfo.t * string list
  | SIAkomaNtoso of LexingInfo.t * string list

let string_of_import = function
  | SILex (_, idents) -> String.concat ~sep:"." idents
  | SIFormex (_, idents) -> String.concat ~sep:"." idents
  | SIAkomaNtoso (_, idents) -> String.concat ~sep:"." idents

let pos_of_import = function
  | SILex (pos, _) -> pos
  | SIFormex (pos, _) -> pos
  | SIAkomaNtoso (pos, _) -> pos

let idents_of_import = function
  | SILex (_, idents) -> idents
  | SIFormex (_, idents) -> idents
  | SIAkomaNtoso (_, idents) -> idents

let extension_of_import = function
  | SILex _ -> ".lex"
  | SIFormex _ -> ".xml"
  | SIAkomaNtoso _ -> ".xml"

let concat_all = function
  | [] -> ""
  | init::idents -> List.fold_left idents ~init ~f:Filename.concat 

let list_imports prog =
  let f = function
    | Lex.SImport (pos, ILex, idents)    -> Some (SILex (pos, idents))
    | Lex.SImport (pos, IFormex, idents) -> Some (SIFormex (pos, idents))
    | Lex.SImport (pos, IAkomaNtoso, idents) -> Some (SIAkomaNtoso (pos, idents))
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
        Errors.import_error
          (sprintf "found cyclic dependency %s"
             (String.concat ~sep:" -> " (seq @ [Filename.concat prefix filename])))
          (pos_of_import import)
      else
        (prefix, filename))
  | None -> Errors.import_error
              (sprintf "cannot find file for importing %s"
                 (string_of_import import))
              (pos_of_import import)

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | Parser.Error ->
     Errors.parser_error "invalid character" (LexingInfo.create1 lexbuf.lex_curr_p)
  | Sys_error msg ->
     Errors.system_error msg (LexingInfo.create1 lexbuf.lex_curr_p)

let parse_module filename: Sformula.t Lex.prog =
   let inx = try In_channel.create filename with
    | Sys_error msg -> eprintf "Cannot open file %s: %s\n" filename msg; exit (-1)
  in
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
        debug (String.concat ~sep:" " (
                          List.map (Label.full_filters full_label)
                            ~f:(fun (kind, ident) -> Lex.string_of_section_kind kind ^ " " ^ ident)));
        match Map.find modules law with
        | Some (MLegalXml xml) ->
          Option.map (LegalXml.find_title xml (List.tl_exn (Label.full_filters full_label)))
            ~f:(fun x -> Tlex.TAFormex (law, x))
        | _ -> None
      end 
    in TSSection (section_kind, full_label, label, title)
  | TSRule (pos, idx, label, type_fixes, rule, None) ->
    let law = Label.qualified_name_of_law label.law in
    let doc_string = begin
        match Map.find modules law with
        | Some (MLegalXml xml) ->
          Option.map (LegalXml.find_data xml (List.tl_exn (Label.full_filters label)))
            ~f:(fun x -> Tlex.TAFormex (law, x))
        | _ -> None
      end 
     in TSRule (pos, idx, label, type_fixes, rule, doc_string)
  | s -> s

let link_formex modules tprog =
  Tlex.{ tprog with tstmts = List.map tprog.tstmts ~f:(link_formex_stmt modules) }

let init_tprog_from_modules modules =
  let f ~key:_ ~data tprog =
    match data with
    | MLex eprog' -> Elex.tprog_import tprog eprog'
    | MLegalXml _ -> tprog in
  Map.fold modules ~init:Tlex.tempty ~f

let rec do_type lexpath ?seq:(seq=[]) b filepath filename =
  let fullname  = Filename.concat filepath filename in
  let seq'      = seq @ [fullname] in
  let sprog     = parse_module fullname in
  let prog      = Lex.map ~f:Formula.init sprog in
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
                          | SILex _    -> MLex (do_type lexpath ~seq:seq' b filepath' filename')
                          | SIFormex _ -> MLegalXml (Formex.read_file filepath' filename')
                          | SIAkomaNtoso _ -> MLegalXml (AkomaNtoso.read_file filepath' filename'))
                       )
                      )
                    ) in
  let modules = Map.of_alist_exn (module String) modules in
  let init  = init_tprog_from_modules modules in
  let tprog = Typing.do_type init prog in
  let tprog = link_formex modules tprog in
  let eprog = Enforceability.do_type modules tprog b in
  eprog

