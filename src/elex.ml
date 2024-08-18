open Core
open Lex
open Tlex

type epattern =
  | EPPresent
  | EPEventually of Interval.t
  | EPAlways of Interval.t
  | EPUntil of Interval.t * Eformula.t
  | EPOnce of Interval.t
  | EPHistorically of Interval.t
  | EPSince of Interval.t * Eformula.t

type erule =
  | EObligation   of Lexing.position * int
  | EPermission   of Lexing.position * int
  | EConstitutive of Lexing.position * (int * int) list
  | EException    of Lexing.position * int
  | EExceptionC   of Lexing.position * int * (int * int) list
  | EScope        of Lexing.position * int

type erule_type = ERTObligation | ERTPermission | ERTConstitutive | ERTException | ERTExceptionC | ERTScope

let erule_type_from_trule_type = function
  | TRTObligation -> ERTObligation
  | TRTPermission -> ERTPermission
  | TRTConstitutive -> ERTConstitutive
  | TRTException -> ERTException
  | TRTExceptionC -> ERTExceptionC
  | TRTScope -> ERTScope

type eref_expr = tref_expr
type epformula = {p: epattern; fs: Eformula.t list}
let epf p fs = {p; fs}

let epattern_of_tpattern tevents = function
  | TPPresent -> EPPresent
  | TPEventually i -> EPEventually i
  | TPAlways i -> EPAlways i
  | TPUntil (i, f) -> EPUntil (i, Eformula.of_tformula tevents f)
  | TPOnce i -> EPOnce i
  | TPHistorically i -> EPHistorically i
  | TPSince (i, f) -> EPSince (i, Eformula.of_tformula tevents f)


let epformula_of_tpformula tevents (tpf: tpformula): epformula = {
  fs = List.map tpf.fs ~f:(Eformula.of_tformula tevents);
  p = epattern_of_tpattern tevents tpf.p
}

type edisjunct = {
  rule_id: int;
  et: erule_type;
  rule_pos: Lexing.position;
  def_positions: Lexing.position list;
  pf: epformula;
  exceptions: Eformula.t list; (* list of predicate *)
  scopes: Eformula.t list; (* list of predicate *)
  fv_renaming: (string, string, String.comparator_witness) Map.t; (* renaming of free variables *)
  params_original: Tformula.TTerm.t list; (* list of the original terms*)
  params_new: Tformula.TTerm.t list; (* list of the new terms*)
}

let edisjunct_of_tdisjunct tevents (td: tdisjunct) = {
  rule_id = td.rule_id;
  et = erule_type_from_trule_type td.tt;
  rule_pos = td.rule_pos;
  def_positions = td.def_positions;
  pf = epformula_of_tpformula tevents td.pf;
  exceptions = List.map td.exceptions ~f:(Eformula.of_tformula tevents);
  scopes = List.map td.scopes ~f:(Eformula.of_tformula tevents);
  fv_renaming = td.fv_renaming;
  params_original = td.params_original;
  params_new = td.params_new;
}

type enf_pformula_sup =
  | ESpfFormula of int
  | ESpfPformula of int (* for until and since, if both sides must be used for enforcement *)
  | ESpfPattern (* for until and since, if it suffices to use the formula in the pattern for enforcement *)

type enf_pformula_cau =
  | ECpfFormulas
  | ECpfPformula (* for until and since, if the formula of the pattern must also be used for enforcement *)
  | ECpfPattern (* for until and since, if it suffices to enforce the formula in the pattern *)

(* A 'lhs' (left-hand side) consists of exception predicates, scope predicates, and a pformula (pattern + formulas) *)
type enf_sup_lhs =
  | ESlhsSPformula of enf_pformula_sup
  | ESlhsCException of int (* leads to suppressing the constitution of an event *)
  | ESlhsSScope of int

type enf_cau_lhs =
  | EClhsAll of enf_pformula_cau

type enf_pformula =
  | EpfSup of enf_pformula_sup
  | EpfCau of enf_pformula_cau

type enf_ecimplication =
  | ESciLhs of enf_sup_lhs
  | ECciRhs of enf_pformula_cau

type enf_ecdefinition =
  | ESd of enf_sup_lhs
  | ECd of enf_cau_lhs

type enf_ecdefinition_dis =
  | ECdd of int * enf_sup_lhs
  | ESdd of enf_cau_lhs list

type ecrule =
  | ECImplication   of int * erule_type * Lexing.position * epformula * Eformula.t list * Eformula.t list * epformula * rule_type * rule_constr list * enf_ecimplication option
  | ECDefinition    of int * erule_type * Lexing.position * epformula * Eformula.t list * Eformula.t list * eref_expr list * Eformula.t * enf_ecdefinition option
  | ECDefinitionDis of (int, edisjunct, Int.comparator_witness) Map.t * Eformula.t * enf_ecdefinition_dis option

type estmt =
  | ESImport  of Lexing.position * string list * import_format
  | ESSection of section_kind * Label.t * string * string tannot option
  | ESRule    of Lexing.position * int * Label.t * (ident * Formula.TypeTerm.t) list * erule * string tannot option
  | ESEvent   of event_type * ident * (Lexing.position * ident * Formula.TypeTerm.t) list * pol * string option
  | ESType    of ident * Formula.TypeTerm.t option * string option
  | ESFunction of ident * (ident * Formula.TypeTerm.t) list * Formula.TypeTerm.t * string option
  | ESNote    of string

type var_types = (ident, Formula.TypeTerm.t, Base.String.comparator_witness) Map.t

type eprog =
  {
    estmts: estmt list;
    ealiases: (ident, Formula.TypeTerm.t option * string option, Base.String.comparator_witness) Map.t; (* maps type aliases to their underlying type *)
    eevents: (ident, tevent, Base.String.comparator_witness) Map.t; (* maps event names to their definitions *)
    efunctions: (ident, tfunction, Base.String.comparator_witness) Map.t;
    variables: (int, var_types, Int.comparator_witness) Map.t; (* maps rule labels to variables used in section *)
    rule_tree: Label.RuleTree.s;
    ecrules: (int, ecrule, Int.comparator_witness) Map.t;
    compilation_order: int list;
    pols: (string, Formula.EnfType.t, Base.String.comparator_witness) Map.t;
  }

let tempty =
  {
    estmts = [];
    ealiases = Map.empty (module String);
    eevents = Map.empty (module String);
    efunctions = Map.empty (module String);
    variables = Map.empty (module Int); 
    rule_tree = Label.RuleTree.empty;
    ecrules = Map.empty (module Int);
    compilation_order = [];
    pols = Map.empty (module String);
  }

let formulas_from_epattern = function
  | EPPresent
  | EPEventually _
  | EPAlways _
  | EPOnce _
  | EPHistorically _ -> []
  | EPUntil (_, f) 
  | EPSince (_, f) -> [f]

let import eprog eprog' =
  let f ~key:_ = function `Both (x, _) | `Left x | `Right x -> Some x in
  { eprog with ealiases   = Map.merge eprog.ealiases eprog'.ealiases ~f;
               eevents    = Map.merge eprog.eevents eprog'.eevents ~f;
               efunctions = Map.merge eprog.efunctions eprog'.efunctions ~f }

let tprog_import tprog eprog' =
  let f ~key:_ = function `Both (x, _) | `Left x | `Right x -> Some x in
  { tprog with taliases   = Map.merge tprog.taliases eprog'.ealiases ~f;
               tevents    = Map.merge tprog.tevents eprog'.eevents ~f;
               tfunctions = Map.merge tprog.tfunctions eprog'.efunctions ~f }

let is_erule = function
  | ESRule _ -> true
  | _ -> false

let get_obligation_params ecrules = function
  | EObligation (_, c_idx) ->
    (match Map.find_exn ecrules c_idx with
      | ECImplication (_, _, _, pf1, _, _, pf2, rt, rcs, _) -> (pf1, pf2, rt, rcs)
      | _ -> assert false)
  | _ -> assert false

let get_permission_params ecrules = function
  | EPermission (_, c_idx) ->
    (match Map.find_exn ecrules c_idx with
      | ECImplication (_, _, _, pf1, _, _, pf2, rt, rcs, _) -> (pf1, pf2, rt, rcs)
      | _ -> assert false)
  | _ -> assert false

let get_constitutive_params ecrules = function
  | EConstitutive (_, cs) ->
    let c_rules = List.map cs ~f:(fun (c_idx,_) -> Map.find_exn ecrules c_idx) in
    let d_indices = List.map cs ~f:(fun (_,d_idx) -> d_idx) in
    let g = List.map c_rules ~f:(fun r -> match r with
              | ECDefinitionDis (_, g, _) -> g
              | _ -> assert false)
    in
    let aux = function
      | ECDefinitionDis (disjuncts, _, _), d_idx -> Map.find_exn disjuncts d_idx
      | _ -> assert false
    in
    let disjuncts = List.zip_exn c_rules d_indices |> List.map ~f:aux in
    let pf = List.map disjuncts ~f:(fun d -> d.pf) |> List.hd_exn in (* TODO (potentially) check that all compilation rule have the same disjunct *)
    (pf, g)
  | _ -> assert false

let get_exception_params ecrules = function
  | EException (_, c_idx) ->
    (match Map.find_exn ecrules c_idx with
      | ECDefinition (_, _, _, pf, _, _,  erefs, _, _) -> (pf, erefs)
      | _ -> assert false)
  | _ -> assert false

let get_scope_params ecrules = function
  | EScope (_, c_idx) ->
    (match Map.find_exn ecrules c_idx with
      | ECDefinition (_, _, _, pf, _, _, erefs, _, _) -> (pf, erefs)
      | _ -> assert false)
  | _ -> assert false

let get_exceptionc_params ecrules = function
  | EExceptionC (_, c_idx_ex, cs) ->
    let c_rule_ex = Map.find_exn ecrules c_idx_ex in
    let c_rules = List.map cs ~f:(fun (c_idx,_) -> Map.find_exn ecrules c_idx) in
    let pf, erefs = (match c_rule_ex with
      | ECDefinition (_, _, _, pf, _, _, erefs, _, _) -> (pf, erefs)
      | _ -> assert false)
    in (* TODO: check that f is the same collection of formulas as in the constitutive rules, and don't just assume so *)
    let g = List.map c_rules ~f:(fun r -> match r with
              | ECDefinitionDis (_, g, _) -> g
              | _ -> assert false)
    in
    (pf, erefs, g)
  | _ -> assert false

let verb_of_erule = function
  | EObligation _ -> "oblige"
  | EPermission _ -> "permit"
  | EConstitutive _ -> "constitute"
  | EException _ 
    | EExceptionC _ -> "except"
  | EScope _ -> "scope"

let string_of_epattern = function
  | EPPresent -> ""
  | EPEventually i -> " eventually " ^ Interval.to_string i 
  | EPAlways i -> " always in the future " ^ Interval.to_string i 
  | EPUntil (i, f) -> " eventually delaying if " ^ Eformula.to_string f ^ " " ^ Interval.to_string i
  | EPOnce i -> " once " ^ Interval.to_string i
  | EPHistorically i -> " always in the past " ^ Interval.to_string i
  | EPSince (i, f) -> " always since " ^ Eformula.to_string f ^ " " ^ Interval.to_string i


let string_of_erule ecrules i erule =
  let to_string f = Etc.tabs (i+1) ^ Eformula.to_string f in
  let reference_to_string ref_ = Etc.tabs (i+1) ^ Lex.string_of_reference ref_ in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:to_string f) ^ "\n" in
  let string_of_reference_list refs =
    String.concat ~sep:"\n" (List.map ~f:reference_to_string refs) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Etc.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_imp_rule verb pf1 pf2 rcs rt =
    Etc.tabs i     ^ "whenever" ^ string_of_epattern pf1.p ^ "\n"
    ^ string_of_formula_list pf1.fs                         
    ^ Etc.tabs i   ^ verb       ^ string_of_epattern pf2.p ^ "\n"
    ^ string_of_formula_list pf2.fs
    ^ Etc.tabs i ^ string_of_rule_type rt (* TODO: check that this prints the rule_type correctly *)
    ^ (if List.is_empty rcs then "" (* TODO: check that this prints the rule_constr list correctly *)
      else Etc.tabs i ^ (string_of_rule_constrs rcs))
  in
  let string_of_cons_rule verb pf g =
    Etc.tabs i     ^ "whenever" ^ string_of_epattern pf.p ^ "\n"
    ^ string_of_formula_list pf.fs  ^ Etc.tabs i   ^ verb  ^ "\n"
    ^ string_of_formula_list g
  in
  let string_of_ref_rule verb pf refs =
    Etc.tabs i     ^ "whenever" ^ string_of_epattern pf.p ^ "\n"
    ^ string_of_formula_list pf.fs                         ^ "\n"
    ^ Etc.tabs i   ^ verb                              ^ "\n"
    ^ string_of_reference_list refs
  in
  let string_of_refc_rule verb pf refs g =
    Etc.tabs i     ^ "whenever"  ^ string_of_epattern pf.p ^ "\n"
    ^ string_of_formula_list pf.fs
    ^ Etc.tabs i   ^ verb                               ^ "\n"
    ^ string_of_reference_list refs                     
    ^ Etc.tabs i   ^ "constitute"                       ^ "\n"
    ^ string_of_formula_list g
  in
  match erule with
  | EObligation _ ->
    let pf1, pf2, rt, rcs = get_obligation_params ecrules erule in
    string_of_imp_rule (verb_of_erule erule) pf1 pf2 rcs rt
  | EPermission _ ->
    let pf1, pf2, rt, rcs = get_obligation_params ecrules erule in
    string_of_imp_rule (verb_of_erule erule) pf1 pf2 rcs rt
  | EConstitutive _ ->
    let pf, g = get_constitutive_params ecrules erule in
    string_of_cons_rule (verb_of_erule erule) pf g
  | EException _ ->
    let pf, erefs = get_exception_params ecrules erule in
    string_of_ref_rule (verb_of_erule erule) pf (List.map ~f:(fun x -> x.ref) erefs)
  | EExceptionC _ ->
    let pf, erefs, g = get_exceptionc_params ecrules erule in
    string_of_refc_rule (verb_of_erule erule) pf (List.map ~f:(fun x -> x.ref) erefs) g
  | EScope _ ->
    let pf, erefs = get_exception_params ecrules erule in
    string_of_ref_rule (verb_of_erule erule) pf (List.map ~f:(fun x -> x.ref) erefs)

let string_of_estmt ecrules ?(i=0) =
  function
  | ESImport (_, idents, _) ->
     Printf.sprintf "import %s"
       (String.concat ~sep:"." idents)
  | ESSection (section_kind, _, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Etc.tabs i)
       (string_of_section_kind section_kind)
       label
       (match title with Some title -> Printf.sprintf ": \"%s\"" (of_annot title) | None -> "")
  | ESRule (_, _, label, type_fixes, rule, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string (of_annot s) i
          | None -> ""
      in
      Printf.sprintf "%srule %s\n%s%s\n%s"
        (Etc.tabs i)
        (Label.qualified_name label)
        (string_of_type_fixes (i+1) type_fixes)
        (string_of_erule ecrules (i+1) rule)
       description
  | ESEvent (event_type, name, typed_args, pol, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
      Printf.sprintf "%s%s %s %s\n%s%s"
          (Etc.tabs i)
          (string_of_pol pol)
          (string_of_event_type event_type)
          name
          description
          (string_of_args typed_args i)
  | ESType (name, typ, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> "" in
      let typ_string =
       match typ with
       | Some tt -> " is " ^ Formula.TypeTerm.to_string tt
       | None -> "" in
     Printf.sprintf "%stype %s%s%s"
       (Etc.tabs i) name typ_string description
  | ESFunction (name, typed_args, return_typ, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string s i
          | None -> ""
     in
     let f (ident, typ) =
       Printf.sprintf "%s : %s" ident (Formula.TypeTerm.value_to_string typ) in
     Printf.sprintf "%sfunction %s(%s) -> %s%s"
       (Etc.tabs i)
       name
       (String.concat ~sep:", " (List.map typed_args ~f))
       (Formula.TypeTerm.value_to_string return_typ)
       description
  | ESNote text -> "note \"" ^ text ^ "\""
    
let string_of_eprog eprog =
  String.concat ~sep:"\n" (List.map eprog.estmts ~f:(string_of_estmt eprog.ecrules))

let print_eprog eprog =
  Stdio.printf "%s\n" (string_of_eprog eprog)
