open Core
open Lex_lib
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | Lexer.SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit (-1)
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let prog = parse_with_error lexbuf in (* program parsed without type information *)
  Lex.print_prog prog;
  (* TOOD: error reporting with lexbuf positions for type checking *)
  let tprog = Typing.do_type prog in (* type check and add type information to program *)
  Compiler.compile tprog; (* compile correctly typed program *)
  In_channel.close inx

let () =
  Command.basic_spec ~summary:"Parse Lex"
    Command.Spec.(empty +> anon ("filename" %: string))
    loop
  |> Command_unix.run
