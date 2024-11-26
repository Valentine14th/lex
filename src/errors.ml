open Core

let debug = ref true (* TODO: set to false if not needed *)
let debug_print ?(f_name=None) msg =
  if !debug then
    match f_name with
    | Some f_name -> Printf.printf "[DEBUG] %s: %s\n" f_name msg
    | None -> Printf.printf "[DEBUG]: %s\n" msg

let lexer_error (msg: string) (pos: LexingInfo.t) =
  eprintf "Lexer error at %s: %s\n" (LexingInfo.to_string pos) msg; exit (-1)

let parser_error (msg: string) (pos: LexingInfo.t) =
  eprintf "Parser error at %s: %s\n" (LexingInfo.to_string pos) msg; exit (-1)

let import_error (msg: string) (pos: LexingInfo.t) =
  eprintf "Import error at %s: %s\n" (LexingInfo.to_string pos) msg; exit (-1)

let type_error (msg: string) (pos: LexingInfo.t) =
  eprintf "Type error at %s: %s\n" (LexingInfo.to_string pos) msg; exit (-1)

let label_error (msg: string) (pos: LexingInfo.t) =
  eprintf "Label error at %s: %s\n" (LexingInfo.to_string pos) msg; exit (-1)

let enf_error (msg: string) (pos: LexingInfo.t option) = match pos with
  | Some pos -> eprintf "Enforcement error at %s: %s\n" (LexingInfo.to_string pos) msg; exit (-1)
  | None -> eprintf "Enforcement error: %s\n" msg; exit (-1)

let reference_error (msg: string) (pos: LexingInfo.t) =
  eprintf "Reference error at %s: %s\n" (LexingInfo.to_string pos) msg; exit(-1)

let compiler_error (msg: string) =
  eprintf "Compiler error: %s\n" msg; exit(-1)

let syntax_error (msg: string) (pos: LexingInfo.t) =
  eprintf "Syntax error at %s: %s\n" (LexingInfo.to_string pos) msg; exit(-1)

let system_error (msg: string) (pos: LexingInfo.t) =
  eprintf "System error at %s: %s\n" (LexingInfo.to_string pos) msg; exit(-1)

let warning msg pos = match pos with
  | Some p -> eprintf "Warning at %s: %s\n" (LexingInfo.to_string p) msg
  | None -> eprintf "Warning: %s\n" msg
