{
  open Lexing
  open Parser

  exception SyntaxError of string

  let keyword_table = Hashtbl.create 53

  let indents = ref []

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
       "formex"       , FORMEX ;
       "akomaNtoso"   , AKOMANTOSO ;
       "function"     , FUNCTION ;
       "event"        , EVENT ;
       "predicate"    , PREDICATE ;
       "functional"   , FUNCTIONAL ;
       "variable"     , VARIABLE ;
       "string"       , TSTRING ;
       "int"          , TINT ;
       "float"        , TFLOAT ;
       "bool"         , TBOOL ;
       "time"         , TTIME ;
       "span"         , TSPAN ;
       "money"        , TMONEY ;
       "type"         , TTYPE ;
       "is"           , IS ;
       "causable"     , TCAUSABLE ;
       "suppressable" , TSUPPRESSABLE ;
       "observable"   , TOBSERVABLE ;
       "transparently", TTRANSPARENTLY ;
       "enforceable"  , TENFORCEABLE ;
       "internal"     , TINTERNAL ;
       "fix"          , FIX ;
       "whenever"     , WHENEVER ;
       "oblige"       , OBLIGE ;
       "permit"       , PERMIT ;
       "constitute"   , CONSTITUTE ;
       "except"       , EXCEPT ;
       "scope"        , SCOPE ;
       "replace"      , REPLACE ;
       "suppressing"  , SUPPRESSING ;
       "causing"      , CAUSING ;
       "within"       , IWITHIN ;
       "before"       , IBEFORE ;
       "strictly"     , ISTRICTLY ;
       "after"        , IAFTER ;
       "between"      , IBETWEEN ;
       "excluded"     , IEXCLUDED ;
       "eventually"   , IEVENTUALLY ;
       "always"       , IALWAYS ;
       "once"         , IONCE ;
       "delaying"     , IDELAYING ;
       "if"           , IIF ;
       "in"           , IIN ;
       "the"          , ITHE ;
       "future"       , IFUTURE ;
       "past"         , IPAST ;
       "SUM"          , SUM ;
       "AVG"          , AVG ;
       "MED"          , MED ;
       "CNT"          , CNT ;
       "MIN"          , MIN ;
       "MAX"          , MAX ;
      ]

}

let white = [' ' '\t']+

let newline = '\r' | '\n' | "\r\n"
let comment = '#' [^ '\r' '\n']*
                                
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let int = ['0'-'9']*
let float1 = ['0'-'9']+ '.' ['0'-'9']*
let float2 = '.' ['0'-'9']+


rule read =
  parse
  | white          { read lexbuf }
  | '\\' white* newline
                   { new_line lexbuf; read lexbuf }
  | ((comment? newline white*)* as n) comment? newline (white+ as w)
                   { repeat new_line lexbuf (1 + count_newlines n) ;
                     let i = update_indent (String.length w) in
                     if i > 0 then
                       NEWUP
                     else if i < 0 then
                       NEWDOWN
                     else
                       NEWHITE }
  | ((comment? newline white*)* as n) comment? newline
                   { repeat new_line lexbuf (1 + count_newlines n);
                     indents := [];
                     NEWLINE }
  | '('            { LPA lexbuf.lex_start_p }
  | ')'            { RPA lexbuf.lex_start_p }
  | ','            { COM }
  | ';'            { SEMICOLON }
  | ':'            { COL }
  | '.'            { DOT }
  | '+'            { ADD }
  | '-'            { SUB lexbuf.lex_start_p }
  | '*'            { MUL }
  | '/'            { DIV }
  | '^'            { POW }
  | "&&"           { LAND }
  | "||"           { LOR }
  | "<-"           { LAR }
  | "<>"           { NEQ }
  | '<'            { LT }
  | '>'            { GT }
  | "and"          { AND lexbuf.lex_start_p }
  | "or"           { OR lexbuf.lex_start_p }
  | "xor"          { XOR }
  | "not"          { NOT lexbuf.lex_start_p }
  | "import"       { IMPORT lexbuf.lex_start_p }
  | "law"          { LAW lexbuf.lex_start_p }
  | "title"        { TITLE lexbuf.lex_start_p }
  | "chapter"      { CHAPTER lexbuf.lex_start_p }
  | "section"      { SECTION lexbuf.lex_start_p }
  | "article"      { ARTICLE lexbuf.lex_start_p }
  | "paragraph"    { PARAGRAPH lexbuf.lex_start_p }
  | "point"        { POINT lexbuf.lex_start_p }
  | "subpoint"     { SUBPOINT lexbuf.lex_start_p }
  | "rule"         { RULE lexbuf.lex_start_p }
  | "note"         { NOTE lexbuf.lex_start_p }
  | "false"        { CFALSE lexbuf.lex_start_p }
  | "true"         { CTRUE lexbuf.lex_start_p }
  | '`'            { read_time (Buffer.create 17) lexbuf }
  | '"'            { read_string (Buffer.create 17) lexbuf }
  | "\"\"\""       { read_docstring (Buffer.create 17) lexbuf }
  | "[" (int as i) "]" { LABEL_LEVEL (int_of_string i) }
  | "FALSE" | "⊥"  { FALSE lexbuf.lex_start_p }
  | "TRUE" | "⊤"   { TRUE lexbuf.lex_start_p }
  | "="            { EQ lexbuf.lex_start_p }
  | "¬" | "NOT"    { NEG lexbuf.lex_start_p }
  | "∧" | "AND"    { AND lexbuf.lex_start_p }
  | "∨" | "OR"     { OR lexbuf.lex_start_p }
  | "→" | "IMPLIES" { IMP lexbuf.lex_start_p }
  | "↔" | "IFF"    { IFF lexbuf.lex_start_p }
  | "∃"  | "EXISTS"{ EXISTS lexbuf.lex_start_p }
  | "∀"  | "FORALL"{ FORALL lexbuf.lex_start_p }
  | "SINCE" | "S"  { SINCE lexbuf.lex_start_p }
  | "UNTIL" | "U"  { UNTIL lexbuf.lex_start_p }
  | "RELEASE" | "R"{ RELEASE lexbuf.lex_start_p }
  | "TRIGGER" |	"T"{ TRIGGER lexbuf.lex_start_p }
  | "NEXT" | "X" | "○" { NEXT lexbuf.lex_start_p }
  | "PREV" | "PREVIOUS" | "Y" | "●" { PREV lexbuf.lex_start_p }
  | "GLOBALLY" | "ALWAYS" | "G" | "□" { ALWAYS lexbuf.lex_start_p }
  | "EVENTUALLY" | "F" | "◊" { EVENTUALLY lexbuf.lex_start_p }
  | "GLOBALLY_PAST" | "HISTORICALLY" | "■" { HISTORICALLY lexbuf.lex_start_p }
  | "ONCE" | "⧫"   { ONCE lexbuf.lex_start_p }
  | '['              { LSB lexbuf.lex_start_p }
  | ']'              { RSB lexbuf.lex_start_p }
  | "INFINITY" | "∞" { INFINITY }
  | ident as id {
        try Hashtbl.find keyword_table id
        with Not_found -> IDENT (lexbuf.lex_start_p, Lexing.lexeme lexbuf)
      }
  | float1 | float2 { FLOAT (lexbuf.lex_start_p, float_of_string (Lexing.lexeme lexbuf)) }
  | int            { INT (lexbuf.lex_start_p, int_of_string (Lexing.lexeme lexbuf)) }
  | (int as i) (("s"|"m"|"h"|"d"|"M"|"y")? as s) { SPAN (lexbuf.lex_start_p, Lextime.Span.of_value_with_unit (int_of_string i) lexbuf.lex_start_p s) }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | comment? (newline|white)* eof   { EOF }

and read_string buf =
  parse
  | '"'       { STRING (lexbuf.lex_start_p, Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }

and read_time buf =
  parse
  | '`'       { TIME (lexbuf.lex_start_p,
                    let contents = Buffer.contents buf in
                    try Lextime.Time.of_string contents
                    with _ -> raise (SyntaxError ("Illegal time expression: `" ^ contents ^ "`"))
                  )
              }
  | [^ '`']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_time buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal time character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("Time is not terminated")) }

(* TODO: remove indentation at the beginning of the line of docstring during parsing *)
and read_docstring buf =
  parse
  | "\"\"\"" { DOCSTRING (Buffer.contents buf) }
  | newline
    { new_line lexbuf;
      Buffer.add_char buf '\n';
      read_docstring buf lexbuf}
  | _
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_docstring buf lexbuf
    }
