%{
    open Lex
    open Formula
%}

%token EOF
%token <Lexing.position * string> IDENT
%token <Lexing.position * int> INT
%token <Lexing.position * Lextime.Span.t> SPAN
%token <Lexing.position * float> FLOAT
%token <Lexing.position * string> STRING
%token <Lexing.position * Lextime.Time.t> TIME
%token COM COL SEMICOLON
%token <Lexing.position> SUB
%token <Lexing.position> NOT
%token LOR LAND ADD MUL DIV POW XOR NEQ LT GT
%token SUM AVG MED CNT MIN MAX
%token <Lexing.position> LPA RPA
%token <Lexing.position> LBR RBR
%token <Lexing.position> LSB RSB
%token <Lexing.position> IMPORT
%token INFINITY
%token FUNCTION EXTERNAL EVENT PREDICATE FUNCTIONAL VARIABLE TSTRING TINT TFLOAT TBOOL TTIME TSPAN TMONEY TCAUSABLE TSUPPRESSABLE TOBSERVABLE TINTERNAL TTRANSPARENTLY TENFORCEABLE
%token IWITHIN IBEFORE ISTRICTLY IAFTER IBETWEEN IEXCLUDED IEVENTUALLY IALWAYS IONCE ISINCE IDELAYING IIF IIN ITHE IFUTURE IPAST
%token IS TTYPE
%token <string> DOCSTRING
%token <Lexing.position> LAW TITLE CHAPTER SECTION ARTICLE PARAGRAPH POINT SUBPOINT
%token <int> LABEL_LEVEL
%token <Lexing.position> RULE
%token <Lexing.position> NOTE
%token FIX WHENEVER OBLIGE PERMIT CONSTITUTE EXCEPT SCOPE
%token CAUSING SUPPRESSING

%token DOT
%token <Lexing.position> FALSE
%token <Lexing.position> TRUE
%token <Lexing.position> CFALSE
%token <Lexing.position> CTRUE
%token <Lexing.position> EQ
%token <Lexing.position> NEG
%token <Lexing.position> AND
%token <Lexing.position> OR
%token <Lexing.position> IMP
%token <Lexing.position> IFF
%token <Lexing.position> EXISTS
%token <Lexing.position> FORALL
%token <Lexing.position> PREV
%token <Lexing.position> NEXT
%token <Lexing.position> ONCE
%token <Lexing.position> EVENTUALLY
%token <Lexing.position> HISTORICALLY
%token <Lexing.position> ALWAYS
%token <Lexing.position> SINCE
%token <Lexing.position> UNTIL
%token <Lexing.position> RELEASE
%token <Lexing.position> TRIGGER

%token FORMEX AKOMANTOSO

%right COL
%right SINCE UNTIL RELEASE TRIGGER
%nonassoc PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS
%nonassoc EXISTS FORALL
%right IFF IMP

%left OR
%left AND
%left LOR
%left LAND
%left XOR
%left EQ NEQ LT GT
%left ADD
%left MUL DIV
%left SUB
%left POW
%nonassoc NOT
%nonassoc NEG


%start <Lex.prog> prog
%%
                    
prog: stmts {$1}

stmts: list(stmt) EOF { { stmts = $1 } }

stmt:
  | IMPORT import                          { SImport ($1, ILex, $2) }
  | IMPORT import_option import            { SImport ($1, $2, $3) }
  | section_kind_and_pos STRING STRING     { SSection (snd $1, fst $1, snd $2, Some (snd $3)) }
  | section_kind_and_pos STRING            { SSection (snd $1, fst $1, snd $2, None) }
  | TTYPE IDENT IS typ                     { SType (fst $2, snd $2, Some $4, None) }
  | TTYPE IDENT IS typ DOCSTRING           { SType (fst $2, snd $2, Some $4, Some $5) }
  | TTYPE IDENT                            { SType (fst $2, snd $2, None, None) }
  | TTYPE IDENT DOCSTRING                  { SType (fst $2, snd $2, None, Some $3) }
  | FUNCTION IDENT LPA fun_args RPA SUB GT type_term { SFunction (fst $2, snd $2, $4, $8, None) }
  | FUNCTION IDENT LPA fun_args RPA SUB GT type_term DOCSTRING { SFunction (fst $2, snd $2, $4, $8, Some $9) }
  | event_def                              { $1 }
  | NOTE STRING                            { SNote ($1, snd $2) }
  | NOTE DOCSTRING                         { SNote ($1, $2) }
  | srule                                  { $1 }

import:
  | IDENT            { [snd $1] }
  | IDENT DOT import { (snd $1)::$3 }

import_option:
  | AKOMANTOSO       { IAkomaNtoso }
  | FORMEX           { IFormex }

section_kind_and_pos:
  | LAW LABEL_LEVEL       { Law $2, $1 }
  | TITLE LABEL_LEVEL     { Title $2, $1 }
  | CHAPTER LABEL_LEVEL   { Chapter $2, $1 }
  | SECTION LABEL_LEVEL   { Section $2, $1 }
  | ARTICLE LABEL_LEVEL   { Article $2, $1 }
  | PARAGRAPH LABEL_LEVEL { Paragraph $2, $1 }
  | POINT LABEL_LEVEL     { Point $2, $1 }
  | SUBPOINT LABEL_LEVEL  { Subpoint $2, $1 }
  | LAW                   { Law 0, $1 }
  | TITLE                 { Title 0, $1 }
  | CHAPTER               { Chapter 0, $1 }
  | SECTION               { Section 0, $1 }
  | ARTICLE               { Article 0, $1 }
  | PARAGRAPH             { Paragraph 0, $1 }
  | POINT                 { Point 0, $1 }
  | SUBPOINT              { Subpoint 0, $1 }

rule_type:
  | TENFORCEABLE { Enforceable }
  | TTRANSPARENTLY TENFORCEABLE { Transparent }
  |              { Vanilla }

pol:
  | TCAUSABLE               { TCau }
  | TSUPPRESSABLE           { TSup }
  | TOBSERVABLE             { TObs }
  | TINTERNAL               { TInternal }
  | TCAUSABLE TSUPPRESSABLE { TCauSup }
  | TSUPPRESSABLE TCAUSABLE { TCauSup }
  |                         { TObs }

typ:
  | TSTRING      { Dom.TStr }
  | TINT         { Dom.TInt }
  | TFLOAT       { Dom.TFloat }
  | TBOOL        { Dom.TBool }
  | TSPAN        { Dom.TSpan }
  | TTIME        { Dom.TTime }
  | TMONEY IDENT { Dom.TMoney (snd $2) }

type_term:
  | typ          { TypeTerm.TypeConst $1 }
  | IDENT        { TypeTerm.TypeVar (snd $1) }

section_kind_with_name:
  | LAW LABEL_LEVEL STRING       { Law $2, snd $3 }
  | TITLE LABEL_LEVEL STRING     { Title $2, snd $3 }
  | CHAPTER LABEL_LEVEL STRING   { Chapter $2, snd $3 }
  | SECTION LABEL_LEVEL STRING   { Section $2, snd $3 }
  | ARTICLE LABEL_LEVEL STRING   { Article $2, snd $3 }
  | PARAGRAPH LABEL_LEVEL STRING { Paragraph $2, snd $3 }
  | POINT LABEL_LEVEL STRING     { Point $2, snd $3 }
  | SUBPOINT LABEL_LEVEL STRING  { Subpoint $2, snd $3 }
  | LAW STRING                   { Law 0, snd $2 }
  | TITLE STRING                 { Title 0, snd $2 }
  | CHAPTER STRING               { Chapter 0, snd $2 }
  | SECTION STRING               { Section 0, snd $2 }
  | ARTICLE STRING               { Article 0, snd $2 }
  | PARAGRAPH STRING             { Paragraph 0, snd $2 }
  | POINT STRING                 { Point 0, snd $2 }
  | SUBPOINT STRING              { Subpoint 0, snd $2 }

reference:
  | LBR nonempty_list(section_kind_with_name) RULE STRING RBR { ($1, ($2, Some (snd $4))) }
  | LBR nonempty_list(section_kind_with_name) RBR { ($1, ($2, None)) }

rule:
  | WHENEVER pattern nonempty_list(e) OBLIGE pattern nonempty_list(e) { Obligation ($3, $2, $6, $5) }
  | WHENEVER pattern nonempty_list(e) PERMIT pattern nonempty_list(e) { Permission ($3, $2, $6, $5) }
  | WHENEVER pattern nonempty_list(e) CONSTITUTE nonempty_list(e)     { Constitutive ($3, $2, $5) }
  | WHENEVER pattern nonempty_list(e) EXCEPT nonempty_list(reference) { Exception ($3, $2, $5) }
  | WHENEVER pattern nonempty_list(e) SCOPE nonempty_list(reference)  { Scope ($3, $2, $5) }

ident:
  | IDENT { snd $1 }

rule_constr:
  | CAUSING list(ident)     { Causing $2 }
  | SUPPRESSING list(ident) { Suppressing $2 }

rule_constrs:
  | separated_list(COM, rule_constr) { $1 }

type_fix:
  | IDENT COL type_term { (snd $1, $3) }

type_fixes:
  | { [] }
  | FIX list(type_fix) { $2 }

fun_args:
  | list(type_fix) { $1 }

srule:
  | RULE DOCSTRING type_fixes rule rule_type rule_constrs        { SRule ($1, None, $3, $4, $5, $6, Some $2) }
  | RULE STRING DOCSTRING type_fixes rule rule_type rule_constrs { SRule ($1, Some (snd $2), $4, $5, $6, $7, Some $3) }
  | RULE type_fixes rule rule_type rule_constrs                  { SRule ($1, None, $2, $3, $4, $5, None) }
  | RULE STRING type_fixes rule rule_type rule_constrs           { SRule ($1, Some (snd $2), $3, $4, $5, $6, None) }

event_def:
  | pol event_type IDENT list(arg)           { SEvent (fst $3, $2, snd $3, $4, $1, None) }
  | pol event_type IDENT DOCSTRING list(arg) { SEvent (fst $3, $2, snd $3, $5, $1, Some $4) }
  | pol FUNCTIONAL functional_event_type IDENT LPA separated_list(COM, arg) RPA SUB GT type_term
    { SEvent (fst $4, $3, snd $4, $6@[Lexing.dummy_pos, "~return_value", $10], $1, None) }
  | pol FUNCTIONAL functional_event_type IDENT LPA separated_list(COM, arg) RPA SUB GT type_term DOCSTRING
    { SEvent (fst $4, $3, snd $4, $6@[Lexing.dummy_pos, "~return_value", $10], $1, Some $11) }

event_type:
  | EXTERNAL EVENT            { Lex.Event (true, Standard) }
  | EVENT                     { Lex.Event (false, Standard) }
  | VARIABLE EXTERNAL EVENT   { Lex.Event (true, Variable) }
  | VARIABLE EVENT            { Lex.Event (false, Variable) }
  | PREDICATE                 { Lex.Predicate }

functional_event_type:
  | EXTERNAL EVENT { Lex.Event (true, Functional) }
  | EVENT          { Lex.Event (false, Functional) }

arg:
  | IDENT COL type_term { (fst $1, snd $1, $3) }

e:
| ee                                   { fst $1, flatten_assoc (snd $1) }

ee:
| LPA e RPA                            { $1, snd $2 }
| TRUE                                 { $1, tt }
| FALSE                                { $1, ff }
| LBR term RBR                         { fst $2, term (snd $2) }
| LBR IDENT EQ aggregation LPA term SEMICOLON vars SEMICOLON e RPA RBR
                                       { fst $2, agg (snd $2) $4 (snd $6) $8 (snd $10) }
| LBR IDENT EQ aggregation LPA term SEMICOLON e RPA RBR
                                       { fst $2, agg (snd $2) $4 (snd $6) [] (snd $8) }
| NEG e                                { $1, neg (snd $2) }
| PREV interval e                      { $1, prev (snd $2) (snd $3) }
| PREV e                               { $1, prev Interval.full (snd $2) }
| NEXT interval e                      { $1, next (snd $2) (snd $3) }
| NEXT e                               { $1, next Interval.full (snd $2) }
| ONCE interval e                      { $1, once (snd $2) (snd $3) }
| ONCE e                               { $1, once Interval.full (snd $2) }
| EVENTUALLY interval e                { $1, eventually (snd $2) (snd $3) }
| EVENTUALLY e                         { $1, eventually Interval.full (snd $2) }
| HISTORICALLY interval e              { $1, historically (snd $2) (snd $3) }
| HISTORICALLY e                       { $1, historically Interval.full (snd $2) }
| ALWAYS interval e                    { $1, always (snd $2) (snd $3) }
| ALWAYS e                             { $1, always Interval.full (snd $2) }
| e AND side e                         { fst $1, conj $3 (snd $1) (snd $4) }
| e AND e                              { fst $1, conj N (snd $1) (snd $3) }
| e OR side e                          { fst $1, disj $3 (snd $1) (snd $4) }
| e OR e                               { fst $1, disj N (snd $1) (snd $3) }
| e IMP side e                         { fst $1, imp $3 (snd $1) (snd $4) }
| e IMP e                              { fst $1, imp N (snd $1) (snd $3) }
| e IFF sides e                        { fst $1, iff (fst $3) (snd $3) (snd $1) (snd $4) }
| e IFF e                              { fst $1, iff N N (snd $1) (snd $3) }
| e SINCE interval side e              { fst $1, since $4 (snd $3) (snd $1) (snd $5) }
| e SINCE interval e                   { fst $1, since N (snd $3) (snd $1) (snd $4) }
| e SINCE side e                       { fst $1, since $3 Interval.full (snd $1) (snd $4) }
| e SINCE e                            { fst $1, since N Interval.full (snd $1) (snd $3) }
| e UNTIL interval side e              { fst $1, until $4 (snd $3) (snd $1) (snd $5) }
| e UNTIL interval e                   { fst $1, until N (snd $3) (snd $1) (snd $4) }
| e UNTIL side e                       { fst $1, until $3 Interval.full (snd $1) (snd $4) }
| e UNTIL e                            { fst $1, until N Interval.full (snd $1) (snd $3) }
| e TRIGGER interval side e            { fst $1, trigger $4 (snd $3) (snd $1) (snd $5) }
| e TRIGGER interval e                 { fst $1, trigger N (snd $3) (snd $1) (snd $4) }
| e TRIGGER side e                     { fst $1, trigger $3 Interval.full (snd $1) (snd $4) }
| e TRIGGER e                          { fst $1, trigger N Interval.full (snd $1) (snd $3) }
| e RELEASE interval side e            { fst $1, release $4 (snd $3) (snd $1) (snd $5) }
| e RELEASE interval e                 { fst $1, release N (snd $3) (snd $1) (snd $4) }
| e RELEASE side e                     { fst $1, release $3 Interval.full (snd $1) (snd $4) }
| e RELEASE e                          { fst $1, release N Interval.full (snd $1) (snd $3) }
| EXISTS vars DOT e %prec EXISTS       { $1, List.fold_right exists (List.tl $2) (exists (List.hd $2) (snd $4)) }
| FORALL vars DOT e %prec FORALL       { $1, List.fold_right forall (List.tl $2) (forall (List.hd $2) (snd $4)) }
| IDENT LPA terms RPA                  { fst $1, predicate (snd $1) (List.map snd $3) }
| e COL ty                             { fst $1, type_ (snd $1) $3 }

side:
| COL IDENT                            { Side.of_string (snd $2) }

sides:
| COL IDENT COM IDENT                  { (Side.of_string (snd $2), Side.of_string (snd $4)) }

term:
| LPA term RPA                         { $1, snd $2 }
| const                                { $1 }
| IDENT                                { fst $1, Term.Var (snd $1) }
| IDENT LPA terms RPA                  { fst $1, Term.App (snd $1, List.map snd $3) }
| unop term                            { fst $1, Term.Unop (snd $1, snd $2) }
| term binop term                      { fst $1, Term.Binop (snd $1, $2, snd $3) }

const:
| INT                                  { fst $1, Term.Const (Int (snd $1)) }
| STRING                               { fst $1, Term.Const (Str (snd $1)) }
| FLOAT                                { fst $1, Term.Const (Float (snd $1)) }
| CTRUE                                { $1, Term.Const (Bool true) }
| CFALSE                               { $1, Term.Const (Bool false) }
| TIME                                 { fst $1, Term.Const (Time (snd $1)) }
| SPAN                                 { fst $1, Term.Const (Span (snd $1)) }
| money                                { fst $1, Term.Const (Money (snd $1)) }

terms:
| trms=separated_list(COM, term)      { trms }

%inline binop:
| ADD   { Term.BAdd }
| SUB   { Term.BSub }
| MUL   { Term.BMul }
| DIV   { Term.BDiv }
| POW   { Term.BPow }
| LAND  { Term.BAnd }
| LOR   { Term.BOr }
| XOR   { Term.BXor }
| EQ    { Term.BEq }
| NEQ   { Term.BNeq }
| LT    { Term.BLt }
| LT EQ { Term.BLeq }
| GT    { Term.BGt }
| GT EQ { Term.BGeq }

%inline unop:
| SUB { $1, Term.USub }
| NOT { $1, Term.UNot }

money:
| IDENT FLOAT { fst $1, Money.( (snd $2) $ (snd $1) ) }
| IDENT INT   { fst $1, Money.( (float_of_int (snd $2)) $ (snd $1) ) }

vars:
| vrs=separated_nonempty_list (COM, ident) { vrs }

ty:
| TCAUSABLE                            { Cau }
| TSUPPRESSABLE                        { Sup }

pattern:
|                                               { PPresent }
| IEVENTUALLY past_interval                     { PEventually $2 }
| IONCE past_interval                           { POnce $2 }
| IALWAYS IIN ITHE IPAST past_interval          { PHistorically $5 }
| IALWAYS IIN ITHE IFUTURE future_interval      { PAlways $5 }
| IEVENTUALLY IDELAYING IIF e future_interval   { PUntil ($5, (snd $4)) }
| IALWAYS ISINCE e future_interval              { PSince ($4, (snd $3)) }

past_interval:
| common_interval                      { $1 }
| IBEFORE SPAN                         { Interval.lclosed_UI (snd $2) }
| ISTRICTLY IBEFORE SPAN               { Interval.lopen_UI (snd $3) }

future_interval:
| common_interval                      { $1 }
| IAFTER SPAN                          { Interval.lclosed_UI (snd $2) }
| ISTRICTLY IAFTER SPAN                { Interval.lopen_UI (snd $3) }

common_interval:
|                                      { Interval.full }
| IWITHIN SPAN                         { Interval.lzero_rclosed_BI (snd $2) }
| IBETWEEN SPAN AND SPAN               { Interval.lclosed_rclosed_BI (snd $2) (snd $4) }
| ISTRICTLY IBETWEEN SPAN AND SPAN     { Interval.lopen_ropen_BI (snd $3) (snd $5) }
| IBETWEEN SPAN AND SPAN IEXCLUDED     { Interval.lclosed_ropen_BI (snd $2) (snd $4) }
| IBETWEEN SPAN IEXCLUDED AND SPAN     { Interval.lopen_rclosed_BI (snd $2) (snd $5) }
					   
interval:
| LSB ib COM ib RSB        { $1, Interval.lclosed_rclosed_BI $2 $4 }
| LSB ib COM ib RPA        { $1, Interval.lclosed_ropen_BI $2 $4 }
| LSB ib COM INFINITY RPA  { $1, Interval.lclosed_UI $2 }
| LPA ib COM ib RSB        { $1, Interval.lopen_rclosed_BI $2 $4 }
| LPA ib COM ib RPA        { $1, Interval.lopen_ropen_BI $2 $4 }
| LPA ib COM INFINITY RPA  { $1, Interval.lopen_UI $2 }

ib:
| SPAN { snd $1 }
| INT  { Lextime.Span.seconds (snd $1) }

aggregation:
| SUM { Aggregation.ASum }
| AVG { Aggregation.AAvg }
| MED { Aggregation.AMed }
| CNT { Aggregation.ACnt }
| MIN { Aggregation.AMin }
| MAX { Aggregation.AMax }
