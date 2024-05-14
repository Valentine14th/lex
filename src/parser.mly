%{
    open Lex
    open Formula
%}

%token EOF
%token <Lexing.position * string> IDENT
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <Lexing.position> LPA RPA
%token COM COL
%token <Lexing.position> LBR RBR
%token <Lexing.position> IMPORT
%token EVENT PREDICATE TSTRING TINT TFLOAT TCAUSABLE TSUPPRESSABLE TOBSERVABLE TINTERNAL TTRANSPARENTLY TENFORCEABLE
%token IS TTYPE
%token <string> DOCSTRING
%token <Lexing.position> LAW TITLE CHAPTER SECTION ARTICLE PARAGRAPH POINT SUBPOINT
%token <int> LABEL_LEVEL
%token <Lexing.position> RULE
%token <Lexing.position> NOTE
%token FIX WHENEVER OBLIGE PERMIT CONSTITUTE EXCEPT SCOPE
%token CAUSING SUPPRESSING

%token DOT
%token <Lexing.position * Interval.t> INTERVAL
%token <Lexing.position> FALSE
%token <Lexing.position> TRUE
%token <Lexing.position> EQCONST
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
  | IMPORT import                          { SImport ($1, ILex, $2) }
  | IMPORT import_option import            { SImport ($1, $2, $3) }
  | section_kind_and_pos STRING STRING     { SSection (snd $1, fst $1, $2, Some $3) }
  | section_kind_and_pos STRING            { SSection (snd $1, fst $1, $2, None) }
  | TTYPE IDENT IS typ                     { SType (fst $2, snd $2, $4, None) }
  | TTYPE IDENT IS typ DOCSTRING           { SType (fst $2, snd $2, $4, Some $5) }
  | event_def                              { $1 }
  | NOTE STRING                            { SNote ($1, $2) }
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
  | TSTRING { TString }
  | TINT    { TInt }
  | TFLOAT  { TFloat }

section_kind_with_name:
  | LAW LABEL_LEVEL STRING       { Law $2, $3 }
  | TITLE LABEL_LEVEL STRING     { Title $2, $3 }
  | CHAPTER LABEL_LEVEL STRING   { Chapter $2, $3 }
  | SECTION LABEL_LEVEL STRING   { Section $2, $3 }
  | ARTICLE LABEL_LEVEL STRING   { Article $2, $3 }
  | PARAGRAPH LABEL_LEVEL STRING { Paragraph $2, $3 }
  | POINT LABEL_LEVEL STRING     { Point $2, $3 }
  | SUBPOINT LABEL_LEVEL STRING  { Subpoint $2, $3 }
  | LAW STRING                   { Law 0, $2 }
  | TITLE STRING                 { Title 0, $2 }
  | CHAPTER STRING               { Chapter 0, $2 }
  | SECTION STRING               { Section 0, $2 }
  | ARTICLE STRING               { Article 0, $2 }
  | PARAGRAPH STRING             { Paragraph 0, $2 }
  | POINT STRING                 { Point 0, $2 }
  | SUBPOINT STRING              { Subpoint 0, $2 }

reference:
  | LBR nonempty_list(section_kind_with_name) RULE STRING RBR { ($1, ($2, Some $4)) }
  | LBR nonempty_list(section_kind_with_name) RBR { ($1, ($2, None)) }

rule:
  | WHENEVER nonempty_list(e) OBLIGE nonempty_list(e)         { Obligation ($2, $4) }
  | WHENEVER nonempty_list(e) PERMIT nonempty_list(e)         { Permission ($2, $4) }
  | WHENEVER nonempty_list(e) CONSTITUTE nonempty_list(e)     { Constitutive ($2, $4) }
  | WHENEVER nonempty_list(e) EXCEPT nonempty_list(reference) { Exception ($2, $4) }
  | WHENEVER nonempty_list(e) SCOPE nonempty_list(reference)  { Scope ($2, $4) }

ident:
  | IDENT { snd $1 }

rule_constr:
  | CAUSING list(ident)     { Causing $2 }
  | SUPPRESSING list(ident) { Suppressing $2 }

rule_constrs:
  | separated_list(COM, rule_constr) { $1 }

type_fix:
  | IDENT COL IDENT { (snd $1, snd $3) }

type_fixes:
  | { [] }
  | FIX list(type_fix) { $2 }

srule:
  | RULE DOCSTRING type_fixes rule rule_type rule_constrs        { SRule ($1, None, $3, $4, $5, $6, Some $2) }
  | RULE STRING DOCSTRING type_fixes rule rule_type rule_constrs { SRule ($1, Some $2, $4, $5, $6, $7, Some $3) }
  | RULE type_fixes rule rule_type rule_constrs                  { SRule ($1, None, $2, $3, $4, $5, None) }
  | RULE STRING type_fixes rule rule_type rule_constrs           { SRule ($1, Some $2, $3, $4, $5, $6, None) }

event_def:
  | pol event_type IDENT list(arg) { SEvent (fst $3, $2, snd $3, $4, $1, None) }
  | pol event_type IDENT DOCSTRING list(arg) { SEvent (fst $3, $2, snd $3, $5, $1, Some $4) }

event_type:
  | EVENT     { Lex.Event }
  | PREDICATE { Lex.Predicate }

arg:
  | IDENT COL IDENT { (fst $1, snd $1, snd $3) }

e:
| ee                                   { fst $1, flatten_assoc (snd $1) }

ee:
| LPA e RPA                            { $1, snd $2 }
| TRUE                                 { $1, tt }
| FALSE                                { $1, ff }
| IDENT EQCONST const                  { fst $1, eqconst (snd $1) (Term.unconst $3)}
| NEG e                                { $1, neg (snd $2) }
| PREV INTERVAL e                      { $1, prev (snd $2) (snd $3) }
| PREV e                               { $1, prev Interval.full (snd $2) }
| NEXT INTERVAL e                      { $1, next (snd $2) (snd $3) }
| NEXT e                               { $1, next Interval.full (snd $2) }
| ONCE INTERVAL e                      { $1, once (snd $2) (snd $3) }
| ONCE e                               { $1, once Interval.full (snd $2) }
| EVENTUALLY INTERVAL e                { $1, eventually (snd $2) (snd $3) }
| EVENTUALLY e                         { $1, eventually Interval.full (snd $2) }
| HISTORICALLY INTERVAL e              { $1, historically (snd $2) (snd $3) }
| HISTORICALLY e                       { $1, historically Interval.full (snd $2) }
| ALWAYS INTERVAL e                    { $1, always (snd $2) (snd $3) }
| ALWAYS e                             { $1, always Interval.full (snd $2) }
| e AND side e                         { fst $1, conj $3 (snd $1) (snd $4) }
| e AND e                              { fst $1, conj N (snd $1) (snd $3) }
| e OR side e                          { fst $1, disj $3 (snd $1) (snd $4) }
| e OR e                               { fst $1, disj N (snd $1) (snd $3) }
| e IMP side e                         { fst $1, imp $3 (snd $1) (snd $4) }
| e IMP e                              { fst $1, imp N (snd $1) (snd $3) }
| e IFF sides e                        { fst $1, iff (fst $3) (snd $3) (snd $1) (snd $4) }
| e IFF e                              { fst $1, iff N N (snd $1) (snd $3) }
| e SINCE INTERVAL side e              { fst $1, since $4 (snd $3) (snd $1) (snd $5) }
| e SINCE INTERVAL e                   { fst $1, since N (snd $3) (snd $1) (snd $4) }
| e SINCE side e                       { fst $1, since $3 Interval.full (snd $1) (snd $4) }
| e SINCE e                            { fst $1, since N Interval.full (snd $1) (snd $3) }
| e UNTIL INTERVAL side e              { fst $1, until $4 (snd $3) (snd $1) (snd $5) }
| e UNTIL INTERVAL e                   { fst $1, until N (snd $3) (snd $1) (snd $4) }
| e UNTIL side e                       { fst $1, until $3 Interval.full (snd $1) (snd $4) }
| e UNTIL e                            { fst $1, until N Interval.full (snd $1) (snd $3) }
| e TRIGGER INTERVAL side e            { fst $1, trigger $4 (snd $3) (snd $1) (snd $5) }
| e TRIGGER INTERVAL e                 { fst $1, trigger N (snd $3) (snd $1) (snd $4) }
| e TRIGGER side e                     { fst $1, trigger $3 Interval.full (snd $1) (snd $4) }
| e TRIGGER e                          { fst $1, trigger N Interval.full (snd $1) (snd $3) }
| e RELEASE INTERVAL side e            { fst $1, release $4 (snd $3) (snd $1) (snd $5) }
| e RELEASE INTERVAL e                 { fst $1, release N (snd $3) (snd $1) (snd $4) }
| e RELEASE side e                     { fst $1, release $3 Interval.full (snd $1) (snd $4) }
| e RELEASE e                          { fst $1, release N Interval.full (snd $1) (snd $3) }
| EXISTS vars DOT e %prec EXISTS       { $1, List.fold_right exists (List.tl $2) (exists (List.hd $2) (snd $4)) }
| FORALL vars DOT e %prec FORALL       { $1, List.fold_right forall (List.tl $2) (forall (List.hd $2) (snd $4)) }
| IDENT LPA terms RPA                  { fst $1, predicate (snd $1) $3 }
| e COL ty                             { fst $1, type_ (snd $1) $3 }

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
| FLOAT                                { Term.Const (Float $1) }

terms:
| trms=separated_list(COM, term)      { trms }

vars:
| vrs=separated_nonempty_list (COM, ident) { vrs }

ty:
| TCAUSABLE                            { Cau }
| TSUPPRESSABLE                        { Sup }



