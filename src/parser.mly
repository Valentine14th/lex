%{
    open Lex
    open Formula
%}

%token EOF
%token <Lexing.position * string> IDENT
%token <int> INT
%token <string> STRING
%token LPA RPA COM COL STAR
%token <Lexing.position> IMPORT
%token EVENT TSTRING TINT TCAUSABLE TSUPPRESSABLE TOBSERVABLE TINTERNAL TENFORCEABLE
%token IS TTYPE
%token <string> DOCSTRING
%token <Lexing.position> LAW TITLE CHAPTER SECTION ARTICLE PARAGRAPH POINT SUBPOINT
%token <int> LABEL_LEVEL
%token <Lexing.position> RULE
%token WHENEVER OBLIGE PERMIT CONSTITUTE EXCEPT
%token CAUSING SUPPRESSING

%token DOT
%token <Interval.t> INTERVAL
%token FALSE
%token TRUE
%token EQCONST
%token NEG
%token AND
%token OR
%token IMP
%token IFF
%token EXISTS
%token FORALL
%token PREV
%token NEXT
%token ONCE
%token EVENTUALLY
%token HISTORICALLY
%token ALWAYS
%token SINCE
%token UNTIL
%token RELEASE
%token TRIGGER

%nonassoc INTERVAL
%right COL
%right SINCE UNTIL RELEASE TRIGGER
%nonassoc PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS
%nonassoc EXISTS FORALL
%right IFF IMP
%left OR
%left AND
%nonassoc NEG

%start <Lex.prog> prog
%%
                    
prog: stmts {$1}

stmts: list(stmt) EOF { { stmts = $1 } }

stmt:
  | IMPORT import                          { SImport ($1, fst $2, snd $2) }
  | section_kind_and_pos STRING STRING     { SSection (snd $1, fst $1, $2, $3) }
  | section_kind_and_pos STRING            { SSection (snd $1, fst $1, $2, "") }
  | TTYPE IDENT IS typ                     { SType (fst $2, snd $2, $4) }
  | event_def                              { $1 }
  | srule                                  { $1 }

import:
  | IDENT            { [snd $1], false }
  | IDENT DOT STAR   { [snd $1], true }
  | IDENT DOT import { let (a, b) = $3 in ((snd $1)::a, b) }

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
  | TSTRING { TString }
  | TINT    { TInt }

rule:
  | WHENEVER nonempty_list(e) OBLIGE nonempty_list(e)      { Obligation ($2, $4) }
  | WHENEVER nonempty_list(e) PERMIT nonempty_list(e)      { Permission ($2, $4) }
  | WHENEVER nonempty_list(e) CONSTITUTE nonempty_list(e)  { Constitutive ($2, $4) }
  | WHENEVER nonempty_list(e) EXCEPT STRING                { Exception ($2, $4) }

ident:
  | IDENT { snd $1 }

rule_constr:
  | CAUSING list(ident)     { Causing $2 }
  | SUPPRESSING list(ident) { Suppressing $2 }

rule_constrs:
  | separated_list(COM, rule_constr) { $1 }

srule:
  | RULE rule rule_type rule_constrs        { SRule ($1, None, $2, $3, $4) }
  | RULE STRING rule rule_type rule_constrs { SRule ($1, Some $2, $3, $4, $5) }

event_def:
  | pol EVENT IDENT list(arg) { SEvent (fst $3, snd $3, $4, $1, None) }
  | pol EVENT IDENT DOCSTRING list(arg) { SEvent (fst $3, snd $3, $5, $1, Some $4) }

arg:
  | IDENT COL IDENT { (fst $1, snd $1, snd $3) }

e:
| LPA e RPA                            { $2 }
| TRUE                                 { tt }
| FALSE                                { ff }
| ident EQCONST const                  { eqconst $1 (Term.unconst $3)}
| NEG e                                { neg $2 }
| PREV INTERVAL e                      { prev $2 $3 }
| PREV e                               { prev Interval.full $2 }
| NEXT INTERVAL e                      { next $2 $3 }
| NEXT e                               { next Interval.full $2 }
| ONCE INTERVAL e                      { once $2 $3 }
| ONCE e                               { once Interval.full $2 }
| EVENTUALLY INTERVAL e                { eventually $2 $3 }
| EVENTUALLY e                         { eventually Interval.full $2 }
| HISTORICALLY INTERVAL e              { historically $2 $3 }
| HISTORICALLY e                       { historically Interval.full $2 }
| ALWAYS INTERVAL e                    { always $2 $3 }
| ALWAYS e                             { always Interval.full $2 }
| e AND side e                         { conj $3 $1 $4 }
| e AND e                              { conj N $1 $3 }
| e OR side e                          { disj $3 $1 $4 }
| e OR e                               { disj N $1 $3 }
| e IMP side e                         { imp $3 $1 $4 }
| e IMP e                              { imp N $1 $3 }
| e IFF sides e                        { iff (fst $3) (snd $3) $1 $4 }
| e IFF e                              { iff N N $1 $3 }
| e SINCE INTERVAL side e              { since $4 $3 $1 $5 }
| e SINCE INTERVAL e                   { since N $3 $1 $4 }
| e SINCE side e                       { since $3 Interval.full $1 $4 }
| e SINCE e                            { since N Interval.full $1 $3 }
| e UNTIL INTERVAL side e              { until $4 $3 $1 $5 }
| e UNTIL INTERVAL e                   { until N $3 $1 $4 }
| e UNTIL side e                       { until $3 Interval.full $1 $4 }
| e UNTIL e                            { until N Interval.full $1 $3 }
| e TRIGGER INTERVAL side e            { trigger $4 $3 $1 $5 }
| e TRIGGER INTERVAL e                 { trigger N $3 $1 $4 }
| e TRIGGER side e                     { trigger $3 Interval.full $1 $4 }
| e TRIGGER e                          { trigger N Interval.full $1 $3 }
| e RELEASE INTERVAL side e            { release $4 $3 $1 $5 }
| e RELEASE INTERVAL e                 { release N $3 $1 $4 }
| e RELEASE side e                     { release $3 Interval.full $1 $4 }
| e RELEASE e                          { release N Interval.full $1 $3 }
| EXISTS vars DOT e %prec EXISTS       { List.fold_right exists (List.tl $2) (exists (List.hd $2) $4) }
| FORALL vars DOT e %prec FORALL       { List.fold_right forall (List.tl $2) (forall (List.hd $2) $4) }
| IDENT LPA terms RPA                  { predicate (snd $1) $3 }
| e COL ty                             { type_ $1 $3 }

side:
| COL IDENT                            { Side.of_string (snd $2) }

sides:
| COL IDENT COM IDENT                  { (Side.of_string (snd $2), Side.of_string (snd $4)) }

term:
| const                                { $1 }
| IDENT                                { Term.Var (snd $1) }

const:
| INT                                  { Term.Const (Int $1) }
| STRING                               { Term.Const (Str $1) }

terms:
| trms=separated_list(COM, term)      { trms }

vars:
| vrs=separated_nonempty_list (COM, ident) { vrs }

ty:
| TCAUSABLE                            { Cau }
| TSUPPRESSABLE                        { Sup }



