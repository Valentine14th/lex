%{
    open Lex
    open Formula
%}

%token EOF NEWLINE
%token NEWUP NEWDOWN NEWHITE
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
%token LAR
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
%token FIX WHENEVER OBLIGE PERMIT CONSTITUTE EXCEPT SCOPE REPLACE
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

stmts: separated_list(NEWLINE, stmt) EOF   { { stmts = $1 } }

stmt:
  | IMPORT import                          { SImport ($1, ILex, $2) }
  | IMPORT import_option import            { SImport ($1, $2, $3) }
  | section_kind_and_pos STRING STRING     { SSection (snd $1, fst $1, snd $2, Some (snd $3)) }
  | section_kind_and_pos STRING            { SSection (snd $1, fst $1, snd $2, None) }
  | TTYPE IDENT IS type_term               { SType (fst $2, snd $2, Some $4, None) }
  | TTYPE IDENT IS type_term NEWUP DOCSTRING{ SType (fst $2, snd $2, Some $4, Some $6) }
  | TTYPE IDENT                            { SType (fst $2, snd $2, None, None) }
  | TTYPE IDENT NEWUP DOCSTRING            { SType (fst $2, snd $2, None, Some $4) }
  | FUNCTION IDENT LPA NEWUP fun_args NEWDOWN RPA SUB GT type_term { SFunction (fst $2, snd $2, $5, $10, None) }
  | FUNCTION IDENT LPA NEWUP fun_args NEWDOWN RPA SUB GT type_term NEWUP DOCSTRING { SFunction (fst $2, snd $2, $5, $10, Some $12) }
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
  | NEWDOWN TENFORCEABLE rule_constrs                { Enforceable, $3 }
  | NEWDOWN TTRANSPARENTLY TENFORCEABLE rule_constrs { Transparent, $4 }
  |                                                  { Vanilla, [] }

pol:
  | TCAUSABLE               { TCau }
  | TSUPPRESSABLE           { TSup }
  | TOBSERVABLE             { TObs }
  | TINTERNAL               { TItl }
  | TCAUSABLE TOBSERVABLE   { TCauObs }
  | TOBSERVABLE TCAUSABLE   { TCauObs }
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
  | typ                                            { TypeTerm.TypeConst $1 }
  | IDENT                                          { TypeTerm.TypeVar (snd $1) }
  | LBR separated_nonempty_list(COM, type_fix) RBR { TypeTerm.TypeSum $2 }

section_kind_with_name:
  | LAW LABEL_LEVEL STRING       { fst $3, (Law $2, snd $3) }
  | TITLE LABEL_LEVEL STRING     { fst $3, (Title $2, snd $3) }
  | CHAPTER LABEL_LEVEL STRING   { fst $3, (Chapter $2, snd $3) }
  | SECTION LABEL_LEVEL STRING   { fst $3, (Section $2, snd $3) }
  | ARTICLE LABEL_LEVEL STRING   { fst $3, (Article $2, snd $3) }
  | PARAGRAPH LABEL_LEVEL STRING { fst $3, (Paragraph $2, snd $3) }
  | POINT LABEL_LEVEL STRING     { fst $3, (Point $2, snd $3) }
  | SUBPOINT LABEL_LEVEL STRING  { fst $3, (Subpoint $2, snd $3) }
  | LAW STRING                   { fst $2, (Law 0, snd $2) }
  | TITLE STRING                 { fst $2, (Title 0, snd $2) }
  | CHAPTER STRING               { fst $2, (Chapter 0, snd $2) }
  | SECTION STRING               { fst $2, (Section 0, snd $2) }
  | ARTICLE STRING               { fst $2, (Article 0, snd $2) }
  | PARAGRAPH STRING             { fst $2, (Paragraph 0, snd $2) }
  | POINT STRING                 { fst $2, (Point 0, snd $2) }
  | SUBPOINT STRING              { fst $2, (Subpoint 0, snd $2) }

reference:
  | RULE STRING                  { (fst $2), ([], Some (snd $2)) }
  | nonempty_list(section_kind_with_name) RULE STRING
                                 { (fst (List.hd $1)), (List.map snd $1, Some (snd $3)) }
  | nonempty_list(section_kind_with_name)
                                 { (fst (List.hd $1)), (List.map snd $1, None) }

rule:
  | WHENEVER pattern NEWUP separated_nonempty_list(NEWHITE, e) NEWDOWN OBLIGE pattern NEWUP separated_nonempty_list(NEWHITE, e) rule_type { Obligation ($4, $2, $9, $7, fst $10, snd $10) }
  | WHENEVER pattern NEWUP separated_nonempty_list(NEWHITE, e) NEWDOWN PERMIT pattern NEWUP separated_nonempty_list(NEWHITE, e) rule_type { Permission ($4, $2, $9, $7, fst $10, snd $10) }
  | WHENEVER pattern NEWUP separated_nonempty_list(NEWHITE, e) NEWDOWN CONSTITUTE NEWUP separated_nonempty_list(NEWHITE, e)               { Constitutive ($4, $2, $8) }
  | WHENEVER pattern NEWUP separated_nonempty_list(NEWHITE, e) NEWDOWN EXCEPT NEWUP separated_nonempty_list(NEWHITE, reference)           { Exception ($4, $2, $8) }
  | WHENEVER pattern NEWUP separated_nonempty_list(NEWHITE, e) NEWDOWN REPLACE NEWUP separated_nonempty_list(NEWHITE, reference) NEWDOWN CONSTITUTE NEWUP separated_nonempty_list(NEWHITE, e)
                                                                                                                                          { ExceptionC ($4, $2, $8, $12) }
  | WHENEVER pattern NEWUP separated_nonempty_list(NEWHITE, e) NEWDOWN SCOPE NEWUP separated_nonempty_list(NEWHITE, reference)            { Scope ($4, $2, $8) }

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
  | FIX NEWUP separated_nonempty_list(NEWHITE, type_fix) NEWDOWN { $3 }

fun_args:
  | list(type_fix) { $1 }

srule:
  | RULE NEWUP DOCSTRING NEWHITE type_fixes rule         { SRule ($1, None, $5, $6, Some $3) }
  | RULE STRING NEWUP DOCSTRING NEWHITE type_fixes rule  { SRule ($1, Some (snd $2), $6, $7, Some $4) }
  | RULE NEWUP type_fixes rule                           { SRule ($1, None, $3, $4, None) }
  | RULE STRING NEWUP type_fixes rule                    { SRule ($1, Some (snd $2), $4, $5, None) }

event_def:
  | pol event_type IDENT NEWUP separated_list(NEWHITE, arg)                   { SEvent (fst $3, $2, snd $3, $5, $1, None) }
  | pol event_type IDENT NEWUP DOCSTRING NEWHITE separated_list(NEWHITE, arg) { SEvent (fst $3, $2, snd $3, $7, $1, Some $5) }
  | pol FUNCTIONAL functional_event_type IDENT LPA NEWUP? separated_list(COM, arg) NEWDOWN? RPA SUB GT type_term
    { SEvent (fst $4, Lex.Event ($3, Functional), snd $4, $7@[Lexing.dummy_pos, "~return_value", $12], $1, None) }
  | pol FUNCTIONAL functional_event_type IDENT LPA NEWUP? separated_list(COM, arg) NEWDOWN? RPA SUB GT type_term NEWUP DOCSTRING
    { SEvent (fst $4, Lex.Event ($3, Functional), snd $4, $7@[Lexing.dummy_pos, "~return_value", $12], $1, Some $14) }
  | pol VARIABLE functional_event_type IDENT COL type_term
    { SEvent (fst $4, Lex.Event ($3, Variable), snd $4, [Lexing.dummy_pos, "~return_value", $6], $1, None) }
  | pol VARIABLE functional_event_type IDENT COL type_term NEWUP DOCSTRING
    { SEvent (fst $4, Lex.Event ($3, Variable), snd $4, [Lexing.dummy_pos, "~return_value", $6], $1, Some $8) }

event_type:
  | EXTERNAL EVENT            { Lex.Event (true, Standard) }
  | EVENT                     { Lex.Event (false, Standard) }
  | PREDICATE                 { Lex.Predicate }

functional_event_type:
  | EXTERNAL EVENT { true }
  | EVENT          { false }

arg:
  | IDENT COL type_term { (fst $1, snd $1, $3) }

e:
| ee                                   { fst $1, flatten_assoc (snd $1) }

ee:
| LPA e RPA                            { $1, snd $2 }
| TRUE                                 { $1, tt }
| FALSE                                { $1, ff }
| term2                                { fst $1, term (snd $1) }
| IDENT LAR aggregation LPA term SEMICOLON vars SEMICOLON e RPA
                                       { fst $1, agg (snd $1) $3 (snd $5) $7 (snd $9) }
| IDENT LAR aggregation LPA term SEMICOLON e RPA
                                       { fst $1, agg (snd $1) $3 (snd $5) [] (snd $7) }
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
| COL IDENT                            { Side.of_string (fst $2) (snd $2) }

sides:
| COL IDENT COM IDENT                  { (Side.of_string (fst $2) (snd $2), Side.of_string (fst $4) (snd $4)) }

term2:
| unop2 term                           { fst $1, Term.Unop (snd $1, snd $2) }
| term binop2 term                     { fst $1, Term.Binop (snd $1, $2, snd $3) }

term:
| LPA term RPA                         { $1, snd $2 }
| const                                { $1 }
| IDENT                                { fst $1, Term.Var (snd $1) }
| IDENT LPA terms RPA                  { fst $1, Term.App (snd $1, List.map snd $3) }
| unop term                            { fst $1, Term.Unop (snd $1, snd $2) }
| term binop term                      { fst $1, Term.Binop (snd $1, $2, snd $3) }
| LBR separated_nonempty_list(COM, field) RBR { $1, Term.Record $2 }
| term DOT IDENT                       { fst $1, Term.Proj (snd $1, snd $3) }

field:
| IDENT COL term                       { snd $1, snd $3 }

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
| ADD    { Term.BAdd }
| SUB    { Term.BSub }
| MUL    { Term.BMul }
| DIV    { Term.BDiv }
| POW    { Term.BPow }
| binop2 { $1 }

%inline binop2:
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
| SUB   { $1, Term.UNot }
| unop2 { $1 }

%inline unop2:
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
