{
  open Lexing
  open Parser

  exception SyntaxError of string

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
  | comment? newline { new_line lexbuf; read lexbuf }
  | '('            { LPA lexbuf.lex_start_p }
  | ')'            { RPA lexbuf.lex_start_p }
  | '{'            { LBR lexbuf.lex_start_p }
  | '}'            { RBR lexbuf.lex_start_p }
  | ','            { COM }
  | ':'            { COL }
  | '.'            { DOT }
  | '+'            { ADD }
  | '-'            { SUB lexbuf.lex_start_p }
  | '*'            { MUL }
  | '/'            { DIV }
  | '^'            { POW }
  | "and"          { AND lexbuf.lex_start_p }
  | "or"           { OR lexbuf.lex_start_p }
  | "xor"          { XOR }
  | "<>"           { NEQ }
  | '<'            { LT }
  | '>'            { GT }
  | "not"          { NOT lexbuf.lex_start_p }
  | '`'            { read_time (Buffer.create 17) lexbuf }
  | '"'            { read_string (Buffer.create 17) lexbuf }
  | "\"\"\""       { read_docstring (Buffer.create 17) lexbuf }
  | "import"       { IMPORT lexbuf.lex_start_p }
  | "formex"       { FORMEX }
  | "akomaNtoso"   { AKOMANTOSO }
  | "event"        { EVENT }
  | "predicate"    { PREDICATE }
  | "string"       { TSTRING }
  | "int"          { TINT }
  | "float"        { TFLOAT }
  | "type"         { TTYPE }
  | "is"           { IS }
  | "causable"     { TCAUSABLE }
  | "suppressable" { TSUPPRESSABLE }
  | "observable"   { TOBSERVABLE }
  | "transparently"{ TTRANSPARENTLY }
  | "enforceable"  { TENFORCEABLE }
  | "internal"     { TINTERNAL }
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
  | "[" (int as i) "]" { LABEL_LEVEL (int_of_string i) }
  | "fix"          { FIX }
  | "whenever"     { WHENEVER }
  | "oblige"       { OBLIGE }
  | "permit"       { PERMIT }
  | "constitute"   { CONSTITUTE }
  | "except"       { EXCEPT }
  | "scope"        { SCOPE }
  | "suppressing"  { SUPPRESSING }
  | "causing"      { CAUSING }
  | "within"       { IWITHIN }
  | "before"       { IBEFORE }
  | "strictly"     { ISTRICTLY }
  | "after"        { IAFTER }
  | "between"      { IBETWEEN }
  | "excluded"     { IEXCLUDED }
  | "eventually"   { IEVENTUALLY }
  | "always"       { IALWAYS }
  | "once"         { IONCE }
  | "delaying"     { IDELAYING }
  | "if"           { IIF }
  | "in"           { IIN }
  | "the"          { ITHE }
  | "future"       { IFUTURE }
  | "past"         { IPAST }
  | "false" | "⊥"  { FALSE lexbuf.lex_start_p }
  | "true" | "⊤"   { TRUE lexbuf.lex_start_p }
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
                   (*  | (['(' '['] as l) white (int as i) white ',' white ((int | "INFINITY" | "∞" | "*") as j) white ([')' ']'] as r)*)
  (*                   { INTERVAL (lexbuf.lex_start_p, make_interval lexbuf l i j r) }*)
  | ident          { IDENT (lexbuf.lex_start_p, Lexing.lexeme lexbuf) }
  | float1 | float2 { FLOAT (lexbuf.lex_start_p, float_of_string (Lexing.lexeme lexbuf)) }
  | int            { INT (lexbuf.lex_start_p, int_of_string (Lexing.lexeme lexbuf)) }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | comment? eof   { EOF }

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
