%{
    open Lex
    open Formula
%}

%token EOF
%token <string> IDENT
%token <int> INT
%token <string> STRING
%token LPA RPA COM COL STAR
%token IMPORT EVENT TSTRING TINT TCAUSABLE TSUPPRESSABLE TOBSERVABLE TINTERNAL TENFORCEABLE
%token CHAPTER ARTICLE PARAGRAPH POINT
%token RULE WHENEVER OBLIGE PERMIT CONSTITUTE EXCEPT
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
  | IMPORT import                        { SImport (fst $2, snd $2) }
  | EVENT IDENT LPA typed_idents RPA pol { SEvent ($2, $4, $6) }
  | section_type STRING                  { SSection ($1, $2, "") }
  | section_type STRING COL STRING       { SSection ($1, $2, $4) }
  | srule                                { $1 }

import:
  | IDENT            { [$1], false }
  | IDENT DOT STAR   { [$1], true }
  | IDENT DOT import { let (a, b) = $3 in ($1::a, b) }

section_type:
  | CHAPTER   { Chapter }
  | ARTICLE   { Article }
  | PARAGRAPH { Paragraph }
  | POINT     { Point }
                      
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

typed_idents:
  | separated_list(COM, typed_ident) { $1 }

typed_ident: IDENT COL typ { ($1, $3) }

typ:
  | TSTRING { TString }
  | TINT    { TInt }

rule:
  | WHENEVER nonempty_list(e) OBLIGE nonempty_list(e)      { Obligation ($2, $4) }
  | WHENEVER nonempty_list(e) PERMIT nonempty_list(e)      { Permission ($2, $4) }
  | WHENEVER nonempty_list(e) CONSTITUTE nonempty_list(e)  { Constitutive ($2, $4) }
  | WHENEVER nonempty_list(e) EXCEPT STRING                { Exception ($2, $4) }

rule_constr:
  | CAUSING list(IDENT)     { Causing $2 }
  | SUPPRESSING list(IDENT) { Suppressing $2 }

rule_constrs:
  | separated_list(COM, rule_constr) { $1 }

srule:
  | RULE rule rule_type rule_constrs        { SRule (None, $2, $3, $4) }
  | RULE STRING rule rule_type rule_constrs { SRule (Some $2, $3, $4, $5) }

e:
| LPA e RPA                            { $2 }
| TRUE                                 { tt }
| FALSE                                { ff }
| IDENT EQCONST const                  { eqconst $1 (Term.unconst $3)}
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
| IDENT LPA terms RPA                  { predicate $1 $3 }
| e COL ty                             { type_ $1 $3 }

side:
| COL IDENT                            { Side.of_string $2 }

sides:
| COL IDENT COM IDENT                  { (Side.of_string $2, Side.of_string $4) }

term:
| const                                { $1 }
| IDENT                                { Term.Var $1 }

const:
| INT                                  { Term.Const (Int $1) }
| STRING                               { Term.Const (Str $1) }

terms:
| trms=separated_list(COM, term)      { trms }

vars:
| vrs=separated_nonempty_list (COM, IDENT) { vrs }

ty:
| TCAUSABLE                            { Cau }
| TSUPPRESSABLE                        { Sup }



