%{
  open Lex
  open Rex
  open Slex
  open Srex
  open Errors
  open OrErrors
  open LexingInfo
  open Sformula

  module Time = MFOTL_lib.Time
  module Interval = MFOTL_lib.Interval
  module Aggregation = MFOTL_lib.Aggregation

  let pf = SPattern.make

  (* exception ParseError of string *)

  let debug_parser = ref false
  let debug msg = if !debug_parser then Errors.debug_print ~f_name:(Some "parser.mly") msg

  let fst_opt_of_last l = if List.length l = 0 then None else Some (fst (List.nth l (List.length l - 1)))
  let last            l = List.nth l (List.length l - 1)
  let fst_of_last     l = fst (last l)

  let error_table = Hashtbl.create 10

  let ok_parse key e =
    Hashtbl.remove error_table key;
    ok e

  let error_parse key loc =
    let new_start, new_loc =
      match Hashtbl.find_opt error_table key with
      | None -> fst loc, loc
      | Some start -> start, (start, snd loc) in
    Hashtbl.replace error_table key new_start;
    error (Errors.parser_error
	     ("cannot parse " ^ key)
	     (LexingInfo.of_loc new_loc))

%}

%token EOF NEWLINE NEWUP NEWDOWN NEWWHITE

/* Tokens: Constants */

%token <LexingInfo.t * string>         IDENT
%token <LexingInfo.t * int>            INT
%token <LexingInfo.t * MFOTL_lib.Time.Span.s> SPAN
%token <LexingInfo.t * float>          FLOAT
%token <LexingInfo.t * string>         STRING
%token <LexingInfo.t * MFOTL_lib.Time.t> TIME
%token <LexingInfo.t>                  FALSE TRUE
%token <LexingInfo.t * string>         DOCSTRING

/* Tokens: symbols */

%token <LexingInfo.t> COM COL SEMICOLON DOT QUOTE
%token <LexingInfo.t> LPA RPA LBR RBR

/* Tokens: program keywords  */

%token <LexingInfo.t> IMPORT RULE NOTE WHENEVER TTYPE IS
%token <LexingInfo.t> FIX OBLIGE CONSTITUTE EXCEPT SCOPE REPLACE CAUSING SUPPRESSING 
%token <LexingInfo.t> LAW TITLE CHAPTER SECTION ARTICLE PARAGRAPH POINT SUBPOINT
%token <LexingInfo.t * int> LABEL_LEVEL
%token <LexingInfo.t> FORMEX AKOMANTOSO

/* Tokens: expression keywords */

%token <LexingInfo.t> EQ SUB NOT AND OR IMP IFF EXISTS FORALL 
%token <LexingInfo.t> PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS SINCE UNTIL RELEASE TRIGGER
%token <LexingInfo.t> ADD MUL DIV POW NEQ LT GT LAR CONC
%token <LexingInfo.t> SUM AVG MED CNT MIN MAX
%token <LexingInfo.t> FUNCTION EXTERNAL EVENT PREDICATE FUNCTIONAL VARIABLE
%token <LexingInfo.t> REFINE LEX REX STRENGTHEN WEAKEN BY ASSUME FULFILLED

/* Tokens: intervals */

%token <MFOTL_lib.Interval.t> INTERVAL

/* Tokens: types */

%token <LexingInfo.t> TSTRING TINT TFLOAT TBOOL TTIME TSPAN TMONEY
%token <LexingInfo.t> TCAUSABLE TSUPPRESSABLE TOBSERVABLE TINTERNAL TTRANSPARENTLY TENFORCEABLE
%token <LexingInfo.t> CONDITIONS EFFECTS EXCEPTIONS SCOPES
%token <LexingInfo.t * int> CONDITION

/* Tokens: patterns */

%token <LexingInfo.t> IWITHIN IBEFORE ISTRICTLY IAFTER IBETWEEN IEXCLUDED IEVENTUALLY IALWAYS IONCE ISINCE IDELAYING IIF IIN ITHE IFUTURE IPAST

/* Priority */

%left COL
%left EXISTS FORALL

%left IFF
%right IMP
%left OR
%left AND
%nonassoc SINCE UNTIL RELEASE TRIGGER
%left ONCE 
%nonassoc LT GT EQ NEQ
%left ADD SUB CONC
%left MUL DIV
%left POW
%left NOT
%left DOT

%start <Slex.sprog Errors.WithErrors.t> prog
%start <Srex.srefi Errors.WithErrors.t> refi
%%

/* Program */

prog:
  | NEWLINE? separated_list(NEWLINE, stmt) EOF
    { WithErrors.(>>=) (witherror_list $2) (fun stmts -> WithErrors.ok { stmts }) }

stmt:
  | import
    { debug "stmt: import";     ok_parse "statement" $1 }
  | label
    { debug "stmt: label";      ok_parse "statement" $1 }
  | type_decl
    { debug "stmt: type_decl";  ok_parse "statement" $1 }
  | fun_decl
    { debug "stmt: fun_decl";   ok_parse "statement" $1 }
  | event_decl
    { debug "stmt: event_decl"; ok_parse "statement" $1 }
  | note
    { debug "stmt: note";       ok_parse "statement" $1 }
  | rule_decl
    { debug "stmt: rule";       ok_parse "statement" $1 }
  | error
    { debug "stmt: error";      error_parse "statement" $loc }

/* Imports */

import:
  | IMPORT import_opt import_name
    { SSImport ($1 +> (fst $3), $2, snd $3) }

import_name:
  | IDENT
    { fst $1, [snd $1] }
  | IDENT DOT import_name
    { fst $1 +> fst $3, (snd $1)::(snd $3) }

import_opt:
  |
    { ILex }
  | AKOMANTOSO
    { IAkomaNtoso }
  | FORMEX
    { IFormex }

/* Labels */

label:
  | section_kind_and_pos STRING STRING
    { SSSection (fst $1, snd $1, snd $2, Some (snd $3)) }
  | section_kind_and_pos STRING
    { SSSection (fst $1, snd $1, snd $2, None) }

section_kind_and_pos:
  | LAW       LABEL_LEVEL
    { $1 +> (fst $2), Law       (snd $2) }
  | TITLE     LABEL_LEVEL
    { $1 +> (fst $2), Title     (snd $2) }
  | CHAPTER   LABEL_LEVEL
    { $1 +> (fst $2), Chapter   (snd $2) }
  | SECTION   LABEL_LEVEL
    { $1 +> (fst $2), Section   (snd $2) }
  | ARTICLE   LABEL_LEVEL
    { $1 +> (fst $2), Article   (snd $2) }
  | PARAGRAPH LABEL_LEVEL
    { $1 +> (fst $2), Paragraph (snd $2) }
  | POINT     LABEL_LEVEL
    { $1 +> (fst $2), Point     (snd $2) }
  | SUBPOINT  LABEL_LEVEL
    { $1 +> (fst $2), Subpoint  (snd $2) }
  | LAW
    { $1            , Law       0 }
  | TITLE
    { $1            , Title     0 }
  | CHAPTER
    { $1            , Chapter   0 }
  | SECTION
    { $1            , Section   0 }
  | ARTICLE
    { $1            , Article   0 }
  | PARAGRAPH
    { $1            , Paragraph 0 }
  | POINT
    { $1            , Point     0 }
  | SUBPOINT
    { $1            , Subpoint  0 }

/* Notes */

note:
  | NOTE STRING
    { SSNote ($1 +> fst $2, snd $2) }
  | NOTE DOCSTRING
    { SSNote ($1 +> fst $2, snd $2) }

/* Type declarations */

type_decl:
  | TTYPE IDENT IS type_term 
    { SSType ($1 +> fst $4, snd $2, Some (snd $4), None) }
  | TTYPE IDENT IS type_term NEWUP DOCSTRING 
    { SSType ($1 +> fst $6, snd $2, Some (snd $4), Some (snd $6)) }
  | TTYPE IDENT
    { SSType ($1 +> fst $2, snd $2, None,          None) }
  | TTYPE IDENT NEWUP DOCSTRING
    { SSType ($1 +> fst $4, snd $2, None,          Some (snd $4)) }

/* Function declarations */

fun_decl:
  | FUNCTION IDENT LPA NEWUP fun_args NEWLINE RPA SUB GT type_term
    { SSFunction (fst $2 +> fst $10, snd $2, $5, snd $10, None) }
  | FUNCTION IDENT LPA NEWUP fun_args NEWLINE RPA SUB GT type_term NEWUP DOCSTRING
    { SSFunction (fst $2 +> fst $12, snd $2, $5, snd $10, Some (snd $12)) }

fun_args:
  | separated_list(NEWWHITE, type_fix)
    { $1 }

/* Event declarations */

event_decl:
  | pol event_type IDENT NEWUP args
    { SSEvent (conclr_opt (fst $1) (fst $2) (fst $5)  (fst $3),
	      snd $2,                     snd $3, snd $5,                              snd $1, None) }
  | pol event_type IDENT
    { SSEvent (conclr_opt (fst $1) (fst $2) None  (fst $3),
	      snd $2,                     snd $3, [],                                  snd $1, None) }
  | pol event_type IDENT NEWUP DOCSTRING NEWWHITE args
    { SSEvent (conclr_opt (fst $1) (fst $2) (fst $7)  (fst $5),
	       snd $2,                     snd $3, snd $7,                              snd $1, Some (snd $5)) }
  | pol event_type IDENT NEWUP DOCSTRING
    { SSEvent (conclr_opt (fst $1) (fst $2) None  (fst $5),
	      snd $2,                     snd $3, [],                                  snd $1, Some (snd $5)) }
  | pol FUNCTIONAL functional_event_type IDENT LPA NEWUP args NEWDOWN RPA SUB GT type_term
    { SSEvent (concl_opt (fst $1) $2 (fst $12),
	      Lex.Event ($3, Functional), snd $4, (snd $7)@["~return_value", snd $12], snd $1, None) }
  | pol FUNCTIONAL functional_event_type IDENT LPA NEWUP args NEWLINE RPA SUB GT type_term NEWUP DOCSTRING
    { SSEvent (concl_opt (fst $1) $2 (fst $12),
	       Lex.Event ($3, Functional), snd $4, (snd $7)@["~return_value", snd $12], snd $1, Some (snd $14)) }
  | pol VARIABLE functional_event_type IDENT COL type_term
    { SSEvent (concl_opt (fst $1) $2 (fst $6),
	      Lex.Event ($3, Variable),   snd $4,    ["~return_value", snd $6],        snd $1, None) }
  | pol VARIABLE functional_event_type IDENT COL type_term NEWUP DOCSTRING
    { SSEvent (concl_opt (fst $1) $2 (fst $8),
	      Lex.Event ($3, Variable),   snd $4,    ["~return_value", snd $6],        snd $1, Some (snd $8)) }

event_type:
  | EXTERNAL EVENT
    { $1 +> $2, Lex.Event (true, Standard) }
  | EVENT
    { $1,       Lex.Event (false, Standard) }
  | PREDICATE
    { $1,       Lex.Predicate }

args:
  | separated_list(NEWWHITE, arg)
    { (fst_opt_of_last $1, List.map snd $1) }

arg:
  | IDENT COL type_term
    { (fst $1 +> fst $3, (snd $1, snd $3)) }

functional_event_type:
  | EXTERNAL EVENT
    { true }
  | EVENT
    { false }

pol:
  | base_pol
    { fst $1, (Option.value ~default:Enftype.bot (snd $1), false) }
  | base_pol TINTERNAL
    { fst $1, (Option.value ~default:Enftype.itl (snd $1), true) }

base_pol:
  | TCAUSABLE
    { Some $1,         Some Enftype.caubot }
  | TSUPPRESSABLE
    { Some $1,         Some Enftype.sup }
  | TOBSERVABLE
    { Some $1,         Some Enftype.obs }
  | TCAUSABLE     TOBSERVABLE
    { Some ($1 +> $2), Some Enftype.cau }
  | TOBSERVABLE   TCAUSABLE
    { Some ($1 +> $2), Some Enftype.cau }
  | TCAUSABLE     TSUPPRESSABLE
    { Some ($1 +> $2), Some Enftype.causup }
  | TSUPPRESSABLE TCAUSABLE
    { Some ($1 +> $2), Some Enftype.causup }
  |
    { None,            None }

/* Rule declarations */

rule_decl:
  | RULE NEWUP DOCSTRING NEWWHITE type_fixes rule
    { SSRule ($1 +> Slex.pos_of_srule $6, None,          $5, $6, Some (snd $3)) }
  | RULE STRING NEWUP DOCSTRING NEWWHITE type_fixes rule
    { SSRule ($1 +> Slex.pos_of_srule $7, Some (snd $2), $6, $7, Some (snd $4)) }
  | RULE NEWUP type_fixes rule
    { SSRule ($1 +> Slex.pos_of_srule $4, None,          $3, $4, None) }
  | RULE STRING NEWUP type_fixes rule
    { SSRule ($1 +> Slex.pos_of_srule $5, Some (snd $2), $4, $5, None) }

type_fixes:
  |
    { [] }
  | FIX NEWUP separated_nonempty_list(NEWWHITE, type_fix) NEWDOWN
    { $3 }

type_fix:
  | IDENT COL type_term
    { (snd $1, snd $3) }

rule:
  | WHENEVER pattern NEWUP es NEWDOWN OBLIGE     pattern NEWUP es rule_type
    { SObligation   (concr_opt $1 (fst $10) (last $9).pos, pf $2 $4, pf $7 $9, fst (snd $10), snd (snd $10)) }
  (*| WHENEVER pattern NEWUP es NEWDOWN PERMIT     pattern NEWUP es rule_type
    { SPermission   (concr_opt $1 (fst $10) (last $9).pos, pf $2 $4, pf $7 $9, fst (snd $10), snd (snd $10)) }*)
  | WHENEVER pattern NEWUP es NEWDOWN CONSTITUTE         NEWUP preds
    { SConstitutive ($1 +> (last $8).pos,                  pf $2 $4, $8) }
  | WHENEVER pattern NEWUP es NEWDOWN EXCEPT             NEWUP ref_exprs
    { SException    ($1 +> fst_of_last $8,                 pf $2 $4, List.map snd $8) }
  | WHENEVER pattern NEWUP es NEWDOWN REPLACE            NEWUP ref_exprs    NEWDOWN CONSTITUTE NEWUP preds
    { SExceptionC   ($1 +> (last $12).pos,                 pf $2 $4, List.map snd $8, $12) }
  | WHENEVER pattern NEWUP es NEWDOWN SCOPE              NEWUP ref_exprs
    { SScope        ($1 +> fst_of_last $8,                 pf $2 $4, List.map snd $8) }

rule_type:
  | NEWDOWN                TENFORCEABLE rule_constrs
    { Some (concr_opt $2 (fst $3) $2), (Enforceable, snd $3) }
  | NEWDOWN TTRANSPARENTLY TENFORCEABLE rule_constrs
    { Some (concr_opt $2 (fst $4) $3), (Transparent, snd $4) }
  | NEWDOWN ASSUME         FULFILLED
    { Some ($2 +> $3),                 (Assumed,     []) }
  |
    { None,                            (Vanilla,     []) }

rule_constrs:
  | separated_list(COM, rule_constr)
    { (fst_opt_of_last $1, List.map snd $1) }

rule_constr:
  | CAUSING     nonempty_list(constrainable)
    { ($1 +> fst_of_last $2, Causing     (List.map snd $2)) }
  | SUPPRESSING nonempty_list(constrainable)
    { ($1 +> fst_of_last $2, Suppressing (List.map snd $2)) }

constrainable:
  | CONDITIONS
    { $1,     CConditions }
  | CONDITION
    { fst $1, CCondition (snd $1) }
  | EFFECTS
    { $1,     CEffects }
  | EXCEPTIONS
    { $1,     CExceptions }
  | SCOPES
    { $1,     CScopes }
  | IDENT
    { fst $1, CEvent (snd $1) }

/* Reference expressions */

ref_exprs:
  | separated_nonempty_list(NEWWHITE, ref_expr)
    { $1 }

ref_expr:
  | RULE STRING
    { $1 +> fst $2,                       Ref.make []                (Some (snd $2)) (fst $2) }
  | nonempty_list(section_kind_with_name) RULE STRING
    { fst (List.hd $1) +> fst $3,         Ref.make (List.map snd $1) (Some (snd $3)) (fst (List.hd $1)) }
  | nonempty_list(section_kind_with_name)
    { fst (List.hd $1) +> fst_of_last $1, Ref.make (List.map snd $1) None (fst (List.hd $1)) }

section_kind_with_name:
  | LAW       label_level STRING
    { fst $3, (Law       $2, snd $3) }
  | TITLE     label_level STRING
    { fst $3, (Title     $2, snd $3) }
  | CHAPTER   label_level STRING
    { fst $3, (Chapter   $2, snd $3) }
  | SECTION   label_level STRING
    { fst $3, (Section   $2, snd $3) }
  | ARTICLE   label_level STRING
    { fst $3, (Article   $2, snd $3) }
  | PARAGRAPH label_level STRING
    { fst $3, (Paragraph $2, snd $3) }
  | POINT     label_level STRING
    { fst $3, (Point     $2, snd $3) }
  | SUBPOINT  label_level STRING
    { fst $3, (Subpoint  $2, snd $3) }

label_level:
  | LABEL_LEVEL
    { snd $1 }
  |
    { 0 }

/* Types */

type_term:
  | typ
    { fst $1, TypeTerm.TConst (snd $1) }
  | IDENT
    { fst $1, TypeTerm.TNamed (snd $1) }
  | QUOTE IDENT
    { $1 +> fst $2, TypeTerm.TVar (snd $2) }
  | LBR separated_nonempty_list(COM, type_fix) RBR
    { $1 +> $3, TypeTerm.TSum   $2 }

typ:
  | TSTRING
    { $1, Dom.TStr }
  | TINT
    { $1, Dom.TInt }
  | TFLOAT
    { $1, Dom.TFloat }
  | TBOOL
    { $1, Dom.TBool }
  | TSPAN
    { $1, Dom.TSpan }
  | TTIME
    { $1, Dom.TTime }
  | TMONEY IDENT
    { $1 +> fst $2, Dom.TMoney (snd $2) }

/* Expressions */

es:
  | separated_nonempty_list(NEWWHITE, e)
    { $1 }

e:
  | LPA e RPA
    { make ($1 +> $3) $2.f }
  | atomic
    { $1 }
  | IDENT LPA terms RPA
    { app (fst $1 +> $4) (snd $1) $3 }
  | agg
    { $1 }
  | e bop side_opt e
    { bop ($1.pos +> $4.pos) $3 $2 $1 $4 }
  | e bop2 side2_opt e
    { bop2 ($1.pos +> $4.pos) $3 $2 $1 $4 }
  | uop e
    { uop (fst $1 +> $2.pos) (snd $1) $2 }
  | EXISTS vars DOT e %prec EXISTS
    { exists ($1 +> $4.pos) (List.map snd $2) $4 }
  | FORALL vars DOT e %prec FORALL
    { forall ($1 +> $4.pos) (List.map snd $2) $4 }
  | e btop interval_opt side_opt e %prec SINCE
    { btop ($1.pos +> $5.pos) $4 $3 $2 $1 $5 }
  | utop interval_opt e %prec ONCE
    { utop (fst $1 +> $3.pos) (snd $1) $2 $3 }
  | e COL ty
    { typ ($1.pos +> fst $3) $1 (snd $3) }
  | LBR separated_nonempty_list(COM, field) RBR
    { record ($1 +> $3) $2 }
  | e DOT IDENT
    { proj ($1.pos +> fst $3) $1 (snd $3) }

atomic:
  | const
    { $1 }
  | IDENT
    { var (fst $1) (snd $1) }

preds:
  | separated_nonempty_list(NEWWHITE, pred)
    { $1 }

pred:
  | IDENT LPA pred_terms RPA
    { app (fst $1 +> $4) (snd $1) $3 }
  | IDENT LPA pred_terms RPA EQ atomic
    { app (fst $1 +> $6.pos) (snd $1) ($3 @ [$6]) }

%inline interval_opt:
  | INTERVAL
    { $1 }
  |
    { Interval.full }

%inline side_opt:
  | side
    { Some $1 }
  |
    { None }

%inline side2_opt:
  | side2
    { Some $1 }
  |
    { None }

agg:
  | IDENT LAR aop LPA e SEMICOLON vars SEMICOLON e RPA
    { agg (fst $1) (snd $1) $3 $5 (List.map snd $7) $9 }
  | IDENT LAR aop LPA e SEMICOLON                e RPA
    { agg (fst $1) (snd $1) $3 $5 []                $7 }

%inline aop:
  | SUM
    { Aggregation.ASum }
  | AVG
    { Aggregation.AAvg }
  | MED
    { Aggregation.AMed }
  | CNT
    { Aggregation.ACnt }
  | MIN
    { Aggregation.AMin }
  | MAX
    { Aggregation.AMax }   

%inline uop:
  | NOT
    { $1, Uop.UNot }
  | SUB
    { $1, Uop.USub }

%inline utop:
  | PREV
    { $1, Utop.UPrev }
  | NEXT
    { $1, Utop.UNext }
  | ONCE
    { $1, Utop.UOnce }
  | EVENTUALLY
    { $1, Utop.UEventually }
  | HISTORICALLY
    { $1, Utop.UHistorically }
  | ALWAYS
    { $1, Utop.UAlways }

%inline bop:
  | AND
    { Bop.BAnd }
  | OR
    { Bop.BOr }
  | IMP
    { Bop.BImp }
  | ADD
    { Bop.BAdd }
  | SUB
    { Bop.BSub }
  | MUL
    { Bop.BMul }
  | DIV
    { Bop.BDiv }
  | POW
    { Bop.BPow }
  | EQ
    { Bop.BEq }
  | NEQ
    { Bop.BNeq }
  | LT
    { Bop.BLt }
  | LT EQ
    { Bop.BLeq }
  | GT
    { Bop.BGt }
  | GT EQ
    { Bop.BGeq }
  | CONC
    { Bop.BConc }

%inline bop2:
  | IFF
    { Bop2.BIff }

%inline btop:
  | SINCE
    { Btop.BSince }
  | UNTIL
    { Btop.BUntil }
  | TRIGGER
    { Btop.BTrigger }
  | RELEASE
    { Btop.BRelease }

side:
  | COL IDENT
    { Side.of_string (snd $2) }

side2:
  | COL IDENT COM IDENT
    { (Side.of_string (snd $2), Side.of_string (snd $4)) }

terms:
  | separated_list(COM, e) { $1 }

pred_terms:
  | separated_list(COM, atomic) { $1 }

field:
  | IDENT COL e
    { snd $1, $3 }

/* Constants */

const:
  | INT
    { const (fst $1) (Int (snd $1)) }
  | STRING
    { const (fst $1) (Str (snd $1)) }
  | FLOAT
    { const (fst $1) (Float (snd $1)) }
  | TRUE
    { const $1       (Bool true) }
  | FALSE
    { const $1       (Bool false) }
  | TIME
    { const (fst $1) (Time (snd $1)) }
  | SPAN
    { const (fst $1) (Span (snd $1)) }
  | money
    { const (fst $1) (Money (snd $1)) }

money:
  | IDENT FLOAT
    { fst $1, Money.( (snd $2) $ (snd $1) ) }
  | IDENT INT
    { fst $1, Money.( (float_of_int (snd $2)) $ (snd $1) ) }

vars:
  | separated_nonempty_list (COM, IDENT) { $1 }

/* Enforcement types */

ty:
  | TCAUSABLE
    { $1, Enftype.cau }
  | TSUPPRESSABLE
    { $1, Enftype.sup }

/* Patterns */

pattern:
  |
    { PPresent }
  | IEVENTUALLY                  future_interval
    { PEventually $2 }
  | IONCE                        past_interval
    { POnce $2 }
  | IALWAYS     IIN ITHE IPAST   past_interval
    { PHistorically $5 }
  | IALWAYS     IIN ITHE IFUTURE future_interval
    { PAlways $5 }
  | IEVENTUALLY IDELAYING IIF e  future_interval
    { PUntil ($5, $4) }
  | IALWAYS     ISINCE        e  past_interval
    { PSince ($4, $3) }

past_interval:
  | common_interval
    { $1 }
  | IBEFORE SPAN
    { Interval.lclosed_UI (snd $2) }
  | ISTRICTLY IBEFORE SPAN
    { Interval.lopen_UI (snd $3) }

future_interval:
  | common_interval
    { $1 }
  | IAFTER SPAN
    { Interval.lclosed_UI (snd $2) }
  | ISTRICTLY IAFTER SPAN
    { Interval.lopen_UI (snd $3) }

common_interval:
  |
    { Interval.full }
  | IWITHIN            SPAN
    { Interval.lclosed_rclosed_BI Time.Span.zero (snd $2) }
  | IBETWEEN           SPAN           AND SPAN
    { Interval.lclosed_rclosed_BI (snd $2)       (snd $4) }
  | ISTRICTLY IBETWEEN SPAN           AND SPAN
    { Interval.lopen_ropen_BI     (snd $3)       (snd $5) }
  | IBETWEEN           SPAN           AND SPAN IEXCLUDED
    { Interval.lclosed_ropen_BI   (snd $2)       (snd $4) }
  | IBETWEEN           SPAN IEXCLUDED AND SPAN
    { Interval.lopen_rclosed_BI   (snd $2)       (snd $5) }

/* Refinement */

refi:
  | NEWLINE? separated_list(NEWLINE, rtmt) EOF
    { WithErrors.(>>=) (witherror_list $2) (fun rtmts -> WithErrors.ok { rtmts }) }

rtmt:
  | REFINE LEX import_name
    { ok (SRRefine ($1 +> $2 +> (fst $3), Some RefineLex, snd $3)) }
  | REFINE REX import_name
    { ok (SRRefine ($1 +> $2 +> (fst $3), Some RefineRex, snd $3)) }
  | REFINE import_name
    { ok (SRRefine ($1 +> (fst $2), None, snd $2)) }
  | rrule_decl
    { ok $1 }
  | type_refi_decl
    { ok $1 }
  | replace_decl
    { ok $1 }
  | assume_decl
    { ok $1 }
  | stmt
    { let* stmt = $1 in ok (SRStmt stmt) }


rrule_decl:
  | RULE NEWUP DOCSTRING NEWWHITE type_fixes rrule
    { SRRule ($1 +> Srex.pos_of_srrule $6, None,          $5, $6, Some (snd $3)) }
  | RULE STRING NEWUP DOCSTRING NEWWHITE type_fixes rrule
    { SRRule ($1 +> Srex.pos_of_srrule $7, Some (snd $2), $6, $7, Some (snd $4)) }
  | RULE NEWUP type_fixes rrule
    { SRRule ($1 +> Srex.pos_of_srrule $4, None,          $3, $4, None) }
  | RULE STRING NEWUP type_fixes rrule
    { SRRule ($1 +> Srex.pos_of_srrule $5, Some (snd $2), $4, $5, None) }

rrule:
  | WHENEVER pattern NEWUP es NEWDOWN REFINE NEWUP preds
    { SRefine ($1 +> (last $8).pos, pf $2 $4, $8) }

type_refi_decl:
  | REFINE TTYPE IDENT IS type_term 
    { SRType ($1 +> fst $5, snd $3, Some (snd $5), None) }
  | REFINE TTYPE IDENT IS type_term NEWUP DOCSTRING 
    { SRType ($1 +> fst $7, snd $3, Some (snd $5), Some (snd $7)) }
  | REFINE TTYPE IDENT
    { SRType ($1 +> fst $3, snd $3, None,          None) }
  | REFINE TTYPE IDENT NEWUP DOCSTRING
    { SRType ($1 +> fst $5, snd $3, None,          Some (snd $5)) }

assume_decl:
  | ASSUME TRUE IDENT
    { SRAssume ($1 +> fst $3, snd $3, true, None) }
  | ASSUME FALSE IDENT
    { SRAssume ($1 +> fst $3, snd $3, false, None) }
  | ASSUME TRUE IDENT NEWUP DOCSTRING
    { SRAssume ($1 +> fst $5, snd $3, true, Some (snd $5)) }
  | ASSUME FALSE IDENT NEWUP DOCSTRING
    { SRAssume ($1 +> fst $5, snd $3, false, Some (snd $5)) }

replace_decl:
  | REPLACE NEWUP replace_kind NEWUP ref_exprs NEWDOWN BY NEWUP ref_exprs
    { SRReplace ($1 +> fst_of_last $9, snd $3, List.map snd $5, List.map snd $9, None) }
  | REPLACE NEWUP replace_kind NEWUP DOCSTRING NEWLINE ref_exprs NEWDOWN BY NEWUP ref_exprs
    { SRReplace ($1 +> fst_of_last $11, snd $3, List.map snd $7, List.map snd $11, Some (snd $5)) }

%inline replace_kind:
  | STRENGTHEN { $1, Strengthen }
  | WEAKEN     { $1, Weaken }
