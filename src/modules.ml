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

let list_imports prog =
  let f = function
    | Lex.SImport (pos, ILex, idents)    -> Some (SILex (pos, idents))
    | Lex.SImport (pos, IFormex, idents) -> Some (SIFormex (pos, idents))
    | Lex.SImport (pos, IAkomaNtoso, idents) -> Some (SIAkomaNtoso (pos, idents))
    | _ -> None
  in List.filter_map ~f Lex.(prog.stmts)

let list_lex_includes sprog =
  let f = function
    | Slex.SSInclude (pos, idents) -> Some (SILex (pos, idents))
    | _ -> None
  in List.filter_map ~f Slex.(sprog.stmts)

let list_rex_includes srefi =
  let f = function
    | Srex.SRStmt (Slex.SSInclude (pos, idents)) -> Some (SILex (pos, idents))
    | _ -> None
  in List.filter_map ~f Srex.(srefi.rtmts)

let suffix_of_import import =
  Util.concat_all_filename (idents_of_import import) ^ extension_of_import import

let check_filename (prefix, filename) =
  Sys_unix.is_file_exn ~follow_symlinks:false (Filename.concat prefix filename)

let find_filename seq import prefixes suffix =
  let open Errors.OrErrors in
  let candidates = List.map prefixes ~f:(fun prefix -> (prefix, suffix)) in
  match List.find candidates ~f:check_filename with
  | Some (prefix, filename) ->
     (if List.mem seq (Filename.concat prefix filename) ~equal:String.equal then
        error (Errors.import_error
                 (sprintf "found cyclic dependency %s"
                    (String.concat ~sep:" -> " (seq @ [Filename.concat prefix filename])))
                 (pos_of_import import))
      else
        ok (prefix, filename))
  | None ->
     error (Errors.import_error
              (sprintf "cannot find file for importing %s"
                 (string_of_import import))
              (pos_of_import import))

let parse_with_error parse_fun lexbuf : 'a Errors.OrErrors.t =
  let open Errors.OrErrors in
  try ok (parse_fun Lexer.read lexbuf) with
  | Parser.Error ->
     error (Errors.parser_error "invalid character" (LexingInfo.create1 lexbuf.lex_curr_p))
  | Sys_error msg ->
     error (Errors.parser_error msg (LexingInfo.create1 lexbuf.lex_curr_p))

let parse_lex_module filename: Slex.sprog Errors.OrErrors.t =
   let inx = try In_channel.create filename with
    | Sys_error msg -> eprintf "Cannot open file %s: %s\n" filename msg; exit (-1)
  in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let prog = parse_with_error Parser.prog lexbuf in
  In_channel.close inx;
  prog

let parse_rex_module filename: Srex.srefi Errors.OrErrors.t =
   let inx = try In_channel.create filename with
    | Sys_error msg -> eprintf "Cannot open file %s: %s\n" filename msg; exit (-1)
  in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let prog = parse_with_error Parser.refi lexbuf in
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

let rec load_lex_with_includes fullname seq' prefixes =
  let open Errors.OrErrors in
  let* sprog    = parse_lex_module fullname in
  let  includes = list_lex_includes sprog in
  let  fns      =
    List.map ~f:(fun incl -> Util.concat_all_filename (idents_of_import incl)) includes in
  let f incl =
    let* (filepath', filename') = find_filename seq' incl prefixes (suffix_of_import incl) in
    let fullname' = Filename.concat filepath' filename' in
    load_lex_with_includes fullname' seq' prefixes in
  let* sprogs   = all (List.map ~f includes) in
  let  incl_map = Map.of_alist_exn (module String) (List.zip_exn fns sprogs) in
  ok (Slex.replace_includes incl_map sprog)

let rec load_rex_with_includes fullname seq' prefixes =
  let open Errors.OrErrors in
  let* srefi    = parse_rex_module fullname in
  let  includes = list_rex_includes srefi in
  let  fns      =
    List.map ~f:(fun incl -> Util.concat_all_filename (idents_of_import incl)) includes in
  let f incl =
    let* (filepath', filename') = find_filename seq' incl prefixes (suffix_of_import incl) in
    let fullname' = Filename.concat filepath' filename' in
    load_rex_with_includes fullname' seq' prefixes in
  let* srefis   = all (List.map ~f includes) in
  let  incl_map = Map.of_alist_exn (module String) (List.zip_exn fns srefis) in
  ok (Srex.replace_includes incl_map srefi)

let rec load_modules imports lexpath b seq' prefixes =
  let open Errors.OrErrors in
  let suffixes  = List.map imports ~f:suffix_of_import in
  let filenames = List.map (List.zip_exn imports suffixes)
                    ~f:(fun (import, suffix) -> find_filename seq' import prefixes suffix) in
  let modules   =
    List.map (List.zip_exn filenames imports)
      ~f:(fun (filepath_filename, import) -> (
            let import_string = string_of_import import in
            let* (filepath', filename') = filepath_filename in
            match import with
            | SILex _ ->
               let* _, eprog = do_type lexpath ~seq:seq' b filepath' filename' in
               ok (import_string, MLex eprog)
            | SIFormex _     ->
               ok (import_string, MLegalXml (Formex.read_file filepath' filename'))
            | SIAkomaNtoso _ ->
               ok (import_string, MLegalXml (AkomaNtoso.read_file filepath' filename'))
          )
      ) in
  all modules
  
and do_type_lex lexpath b fullname seq' prefixes : (Typing.t * Elex.eprog) Errors.OrErrors.t =
  let open Errors.OrErrors in
  let* sprog    = load_lex_with_includes fullname seq' prefixes in
  let  prog     = Slex.to_prog sprog in
  let  imports  = list_imports prog in
  let* modules  = load_modules imports lexpath b seq' prefixes in
  let  modules  = Map.of_alist_exn (module String) modules in
  let  init     = init_tprog_from_modules modules in
  let* s, tprog = of_witherror (Typing.do_type init prog) in
  let  tprog    = link_formex modules tprog in
  let* eprog    = Enforceability.do_type tprog b in
  ok (s, eprog)

and do_type_rex lexpath b fullname seq seq' prefixes : (Typing.t * Elex.eprog) Errors.OrErrors.t =
  let open Errors.OrErrors in
  let* srefi         = load_rex_with_includes fullname seq' prefixes in
  let  refi          = Srex.to_refi srefi in
  let  prog_import   = SILex (LexingInfo.dummy, refi.lex_file) in
  let  prog_suffix   = suffix_of_import prog_import in
  let* filepath, prog_filename = find_filename seq' prog_import prefixes prog_suffix in
  let* s, _          = do_type lexpath ~seq b filepath prog_filename in
  let* s, trefi      = of_witherror (Rtyping.do_type s refi) in
  let* erefi         = Refinement.do_type trefi b in
  ok (s, erefi.eprog)

and do_type lexpath ?seq:(seq=[]) b filepath filename : (Typing.t * Elex.eprog) Errors.OrErrors.t =
  let fullname = Filename.concat filepath filename in
  let seq'     = seq @ [fullname] in
  let prefixes = filepath :: lexpath in
  if String.is_suffix filename ~suffix:".rex" then
    do_type_rex lexpath b fullname seq seq' prefixes
  else 
    do_type_lex lexpath b fullname seq' prefixes
