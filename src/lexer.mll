{
  open Lexing
  open Parser

  module Time = MFOTL_lib.Time

  let (+>) = LexingInfo.(+>)

  let debug_lexer = ref false
  let debug msg = if !debug_lexer then Errors.debug_print ~f_name:(Some "lexer.mll") msg

  let keyword_table = Hashtbl.create 53

  let indents = ref []

  let info lexbuf = LexingInfo.create lexbuf.lex_start_p lexbuf.lex_curr_p
  let info1 lexbuf = LexingInfo.create1 lexbuf.lex_start_p

  let make_interval lexbuf =
    MFOTL_lib.Interval.lex (fun () -> Errors.fatal (Errors.lexer_error "interval lexing did not succeed" (info lexbuf)))

  let rec update_indent i =
    match !indents with
    | []                 -> indents := [i]; 1
    | j :: t when i < j  -> indents := t; (update_indent i) - 1
    | j :: _ when i == j -> 0
    | j :: t             -> indents := i :: j :: t; 1


  let rec repeat f x = function
    | i when i <= 0 -> ()
    | i             -> f x; repeat f x (i-1)

  let rec count_newlines ?(i=0) s =
    if String.length s >= i+2 && String.get s i == '\r' && String.get s (i+1) == '\n' then
      1 + count_newlines ~i:(i+2) s
    else if String.length s >= i+1 && (String.get s i == '\r' || String.get s i == '\n') then
      1 + count_newlines ~i:(i+1) s
    else if String.length s >= i+2 then
      count_newlines ~i:(i+1) s
    else
      0

  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      [
       "formex"       , (fun b -> FORMEX b) ;
       "akomaNtoso"   , (fun b -> AKOMANTOSO b) ;
       "function"     , (fun b -> FUNCTION b) ;
       "event"        , (fun b -> EVENT b) ;
       "predicate"    , (fun b -> PREDICATE b) ;
       "functional"   , (fun b -> FUNCTIONAL b) ;
       "variable"     , (fun b -> VARIABLE b) ;
       "string"       , (fun b -> TSTRING b) ;
       "int"          , (fun b -> TINT b) ;
       "float"        , (fun b -> TFLOAT b) ;
       "bool"         , (fun b -> TBOOL b) ;
       "time"         , (fun b -> TTIME b) ;
       "span"         , (fun b -> TSPAN b) ;
       "money"        , (fun b -> TMONEY b) ;
       "type"         , (fun b -> TTYPE b) ;
       "is"           , (fun b -> IS b) ;
       "causable"     , (fun b -> TCAUSABLE b) ;
       "suppressable" , (fun b -> TSUPPRESSABLE b) ;
       "observable"   , (fun b -> TOBSERVABLE b) ;
       "transparently", (fun b -> TTRANSPARENTLY b) ;
       "enforceable"  , (fun b -> TENFORCEABLE b) ;
       "internal"     , (fun b -> TINTERNAL b) ;
       "fix"          , (fun b -> FIX b) ;
       "oblige"       , (fun b -> OBLIGE b) ;
       "constitute"   , (fun b -> CONSTITUTE b) ;
       "except"       , (fun b -> EXCEPT b) ;
       "scope"        , (fun b -> SCOPE b) ;
       "replace"      , (fun b -> REPLACE b) ;
       "suppressing"  , (fun b -> SUPPRESSING b) ;
       "causing"      , (fun b -> CAUSING b) ;
       "conditions"   , (fun b -> CONDITIONS b) ;
       "effects"      , (fun b -> EFFECTS b) ;
       "exceptions"   , (fun b -> EXCEPTIONS b) ;
       "scopes"       , (fun b -> SCOPES b) ;
       "within"       , (fun b -> IWITHIN b) ;
       "before"       , (fun b -> IBEFORE b) ;
       "strictly"     , (fun b -> ISTRICTLY b) ;
       "after"        , (fun b -> IAFTER b) ;
       "between"      , (fun b -> IBETWEEN b) ;
       "excluded"     , (fun b -> IEXCLUDED b) ;
       "eventually"   , (fun b -> IEVENTUALLY b) ;
       "always"       , (fun b -> IALWAYS b) ;
       "once"         , (fun b -> IONCE b) ;
       "delaying"     , (fun b -> IDELAYING b) ;
       "if"           , (fun b -> IIF b) ;
       "in"           , (fun b -> IIN b) ;
       "the"          , (fun b -> ITHE b) ;
       "future"       , (fun b -> IFUTURE b) ;
       "past"         , (fun b -> IPAST b) ;
       "SUM"          , (fun b -> SUM b) ;
       "AVG"          , (fun b -> AVG b) ;
       "MED"          , (fun b -> MED b) ;
       "CNT"          , (fun b -> CNT b) ;
       "MIN"          , (fun b -> MIN b) ;
       "MAX"          , (fun b -> MAX b) ;
       "refine"       , (fun b -> REFINE b) ;
       "lex"          , (fun b -> LEX b) ;
       "rex"          , (fun b -> REX b) ;
       "strengthen"   , (fun b -> STRENGTHEN b) ;
       "weaken"       , (fun b -> WEAKEN b) ;
       "by"           , (fun b -> BY b) ;
       "assume"       , (fun b -> ASSUME b) ;
       "fulfilled"    , (fun b -> FULFILLED b) ;
      ]
}

let white   = [' ' '\t']+

let newline = '\r' | '\n' | "\r\n"
let comment = '#' [^ '\r' '\n']*
                                
let ident   = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* '\''*
let int     = ['0'-'9']+
let float1  = ['0'-'9']+ '.' ['0'-'9']*
let float2  = '.' ['0'-'9']+

rule read =
  parse
  | (comment? newline white*)* eof
     { debug "EOF"; EOF }
  | white
    { debug "white space 1";
      read lexbuf }
  | '\\' white* newline
    { debug "white space 2";
      new_line lexbuf;
      read lexbuf }
  | ((comment? newline white*)* as n) comment? newline (white+ as w) as comment
    { debug ("comment 1" ^ comment);
      repeat new_line lexbuf (1 + count_newlines n);
      let l = String.length w in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_bol = lexbuf.lex_curr_p.pos_bol - l + 1 };
      match update_indent l with
      | i when i > 0 -> debug "up"; NEWUP
      | i when i < 0 -> debug "down"; NEWDOWN
      | _            -> debug "white"; NEWWHITE }
  | ((comment? newline white*)* as n) comment? newline as comment
    { debug ("comment 2" ^ comment);
      repeat new_line lexbuf (1 + count_newlines n);
      indents := [];
      NEWLINE }
  | '('                                          { LPA (info1 lexbuf) }
  | ')'                                          { RPA (info1 lexbuf) }
  | ','                                          { COM (info1 lexbuf) }
  | ';'                                          { SEMICOLON (info1 lexbuf) }
  | ':'                                          { COL (info1 lexbuf) }
  | '.'                                          { DOT (info1 lexbuf) }
  | '+'                                          { ADD (info1 lexbuf) }
  | '-'                                          { SUB (info1 lexbuf) }
  | '*'                                          { MUL (info1 lexbuf) }
  | '/'                                          { DIV (info1 lexbuf) }
  | '^'                                          { POW (info1 lexbuf) }
  | '\''                                         { QUOTE (info1 lexbuf) }
  | "<-"                                         { LAR (info1 lexbuf) }
  | "<>"                                         { NEQ (info1 lexbuf) }
  | '<'                                          { LT (info1 lexbuf) }
  | '>'                                          { GT (info1 lexbuf) }
  | "and"                                        { AND (info lexbuf) }
  | "or"                                         { OR (info lexbuf) }
  | "not"                                        { NOT (info lexbuf) }
  | "import"                                     { IMPORT (info lexbuf) }
  | "law"                                        { LAW (info lexbuf) }
  | "title"                                      { TITLE (info lexbuf) }
  | "chapter"                                    { CHAPTER (info lexbuf) }
  | "section"                                    { SECTION (info lexbuf) }
  | "article"                                    { ARTICLE (info lexbuf) }
  | "paragraph"                                  { debug "paragraph"; PARAGRAPH (info lexbuf) }
  | "point"                                      { debug "point"; POINT (info lexbuf) }
  | "subpoint"                                   { SUBPOINT (info lexbuf) }
  | "rule"                                       { RULE (info lexbuf) }
  | "whenever"                                   { WHENEVER (info lexbuf) }
  | "note"                                       { NOTE (info lexbuf) }
  | '`'                                          { read_time (Buffer.create 17) (info1 lexbuf) lexbuf }
  | '"'                                          { read_string (Buffer.create 17) (info1 lexbuf) lexbuf }
  | "\"\"\""                                     { read_docstring (Buffer.create 17) (info lexbuf) lexbuf }
  | "condition[" (int as i) "]"                  { CONDITION (info lexbuf, int_of_string i) }
  | "[" (int as i) "]"                           { LABEL_LEVEL (info lexbuf, int_of_string i) }
  | (['(' '['] as l) white* (int as i) white* (ident? as u) white* ',' white* ((int | "INFINITY" | "∞" | "*") as j) white* (ident? as v) white* ([')' ']'] as r)                       { INTERVAL (make_interval lexbuf l i u j v r) }
  | "false"                          | "⊥"       { FALSE (info lexbuf) }
  | "true"                           | "⊤"       { TRUE (info lexbuf) }
  | '='                                          { EQ (info lexbuf) }
  | "NOT"                            | "¬"       { NOT (info lexbuf) }
  | "AND"                            | "∧"       { AND (info lexbuf) }
  | "OR"                             | "∨"       { OR (info lexbuf) }
  | "IMPLIES"                        | "→"      { IMP (info lexbuf) }
  | "IFF"                            | "↔"      { IFF (info lexbuf) }
  | "EXISTS"                         | "∃"       { EXISTS (info lexbuf) }
  | "FORALL"                         | "∀"       { FORALL (info lexbuf) }
  | "SINCE"                          | "S"       { SINCE (info lexbuf) }
  | "UNTIL"                          | "U"       { UNTIL (info lexbuf) }
  | "RELEASE"                        | "R"       { RELEASE (info lexbuf) }
  | "TRIGGER"                        | "T"       { TRIGGER (info lexbuf) }
  | "NEXT"                           | "X" | "○" { NEXT (info lexbuf) }
  | "PREV"          | "PREVIOUS"     | "Y" | "●" { PREV (info lexbuf) }
  | "GLOBALLY"      | "ALWAYS"       | "G" | "□" { ALWAYS (info lexbuf) }
  | "EVENTUALLY"                     | "F" | "◊" { EVENTUALLY (info lexbuf) }
  | "GLOBALLY_PAST" | "HISTORICALLY" | "■"       { HISTORICALLY (info lexbuf) }
  | "ONCE"                           | "⧫"       { ONCE (info lexbuf) }
  | ident as id
    {
      debug id;
      try (Hashtbl.find keyword_table id) (info lexbuf)
      with Not_found -> IDENT (info lexbuf, Lexing.lexeme lexbuf)
    }
  | float1 | float2
    { FLOAT (info lexbuf, float_of_string (Lexing.lexeme lexbuf)) }
  | int
     { INT (info lexbuf, int_of_string (Lexing.lexeme lexbuf)) }
  | (int as i) (("s"|"m"|"h"|"d"|"M"|"y")? as s)
     { SPAN (info lexbuf, Time.Span.make i s) }
  | _
     { Errors.fatal (Errors.lexer_error ("Unexpected character: " ^ Lexing.lexeme lexbuf) (info1 lexbuf)) }

and read_string buf i =
  parse
  | '"'       { STRING (i +> info1 lexbuf, Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/';    read_string buf i lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\';   read_string buf i lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b';   read_string buf i lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf i lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n';   read_string buf i lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r';   read_string buf i lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t';   read_string buf i lexbuf }
  | [^ '"' '\\']+ { Buffer.add_string buf (Lexing.lexeme lexbuf); read_string buf i lexbuf }
  | _         { Errors.fatal (Errors.lexer_error ("Illegal character in string: " ^ Lexing.lexeme lexbuf) (info1 lexbuf)) }
  | eof       { Errors.fatal (Errors.lexer_error "This string is never terminated" i) }

and read_time buf i =
  parse
  | '`' { TIME (i +> info1 lexbuf,
                let contents = Buffer.contents buf in
                try Time.of_string contents
                with _ -> Errors.fatal (Errors.lexer_error ("Illegal time expression: `" ^ contents ^ "`") (i +> info1 lexbuf))) }
  | [^ '`']+ { Buffer.add_string buf (Lexing.lexeme lexbuf); read_time buf i lexbuf }
  | _   { Errors.fatal (Errors.lexer_error ("Illegal time character: " ^ Lexing.lexeme lexbuf) (info1 lexbuf)) }
  | eof { Errors.fatal (Errors.lexer_error "This time expression is never terminated" i) }

(* TODO: remove indentation at the beginning of the line of docstring during parsing *)
and read_docstring buf i =
  parse
  | "\"\"\"" { DOCSTRING (i +> info lexbuf, Buffer.contents buf) }
  | newline  { new_line lexbuf;
               Buffer.add_char buf '\n';
               read_docstring buf i lexbuf}
  | _        { Buffer.add_string buf (Lexing.lexeme lexbuf);
               read_docstring buf i lexbuf }
