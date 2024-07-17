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
  | EObligation   of int
  | EPermission   of int
  | EConstitutive of (int * int) list
  | EException    of int
  | EExceptionC   of (int * (int * int) list)
  | EScope        of int

type erule_compilation =
  | ECImplication   of int * (Lexing.position * Eformula.t) list * (Lexing.position * Eformula.t) list * (Lexing.position * Eformula.t) list * epattern * (Lexing.position * Eformula.t) list * epattern * rule_type * rule_constr list
  | ECDefinition    of int * (Lexing.position * Eformula.t) list * (Lexing.position * Eformula.t) list * (Lexing.position * Eformula.t) list * epattern * (Lexing.position * Label.t * Lex.reference) list * Eformula.t
  | ECDefinitionDis of (int, (int * Lexing.position * (Lexing.position * Eformula.t) list * (Lexing.position * Eformula.t) list * (Lexing.position * Eformula.t) list * epattern), Int.comparator_witness) Map.t * Eformula.t

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
    compilation_rules: (int, erule_compilation, Int.comparator_witness) Map.t;
  }

let tempty =
  {
    estmts = [];
    ealiases = Map.empty (module String);
    eevents = Map.empty (module String);
    efunctions = Map.empty (module String);
    variables = Map.empty (module Int); 
    rule_tree = Label.RuleTree.empty;
    compilation_rules = Map.empty (module Int);
  }


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

let get_obligation_params compilation_rules = function
  | EObligation c_idx ->
    (match Map.find_exn compilation_rules c_idx with
      | ECImplication (_, f, _, _, p, g, q, rt, rcs) -> (f, p, g, q, rt, rcs)
      | _ -> assert false)
  | _ -> assert false

let get_permission_params compilation_rules = function
  | EPermission c_idx ->
    (match Map.find_exn compilation_rules c_idx with
      | ECImplication (_, f, _, _, p, g, q, rt, rcs) -> (f, p, g, q, rt, rcs)
      | _ -> assert false)
  | _ -> assert false

let get_constitutive_params compilation_rules = function
  | EConstitutive cs ->
    let c_rules = List.map cs ~f:(fun (c_idx,_) -> Map.find_exn compilation_rules c_idx) in
    let d_indices = List.map cs ~f:(fun (_,d_idx) -> d_idx) in
    let g = List.map c_rules ~f:(fun r -> match r with
              | ECDefinitionDis (_,g) -> Lexing.dummy_pos, g (* TODO: (maybe) get something better than a dummy position *)
              | _ -> assert false)
    in
    let aux = function
      | ECDefinitionDis (disjuncts,_), d_idx -> Map.find_exn disjuncts d_idx
      | _ -> assert false
    in
    let disjuncts = List.zip_exn c_rules d_indices |> List.map ~f:aux in
    let f,p = List.map disjuncts ~f:(fun (_,_,f,_,_,p) -> (f,p)) |> List.hd_exn in (* TODO (potentially) check that all compilation rule have the same disjunct *)
    (f,p,g)
  | _ -> assert false

let get_exception_params compilation_rules = function
  | EException c_idx ->
    (match Map.find_exn compilation_rules c_idx with
      | ECDefinition (_, f, _, _, p, erefs, _) -> (f, p, erefs)
      | _ -> assert false)
  | _ -> assert false

let get_scope_params compilation_rules = function
  | EScope c_idx ->
    (match Map.find_exn compilation_rules c_idx with
      | ECDefinition (_, f, _, _, p, erefs, _) -> (f, p, erefs)
      | _ -> assert false)
  | _ -> assert false

let get_exceptionc_params compilation_rules = function
  | EExceptionC (c_idx_ex, cs) ->
    let c_rule_ex = Map.find_exn compilation_rules c_idx_ex in
    let c_rules = List.map cs ~f:(fun (c_idx,_) -> Map.find_exn compilation_rules c_idx) in
    let f, p, erefs = (match c_rule_ex with
      | ECDefinition (_, f, _, _, p, erefs, _) -> (f, p, erefs)
      | _ -> assert false)
    in (* TODO: check that f is the same collection of formulas as in the constitutive rules, and don't just assume so *)
    let g = List.map c_rules ~f:(fun r -> match r with
              | ECDefinitionDis (_,g) -> Lexing.dummy_pos, g (* TODO: (maybe) get something better than a dummy position *)
              | _ -> assert false)
    in
    (f, p, erefs, g)
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


let string_of_erule compilation_rules i erule =
  let to_string f = Etc.tabs (i+1) ^ Eformula.to_string f in
  let reference_to_string ref_ = Etc.tabs (i+1) ^ Lex.string_of_reference ref_ in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:(fun (_,f') -> to_string f') f) ^ "\n" in
  let string_of_reference_list refs =
    String.concat ~sep:"\n" (List.map ~f:reference_to_string refs) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Etc.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_imp_rule verb f p g q rcs rt =
    Etc.tabs i     ^ "whenever" ^ string_of_epattern p ^ "\n"
    ^ string_of_formula_list f                         
    ^ Etc.tabs i   ^ verb       ^ string_of_epattern q ^ "\n"
    ^ string_of_formula_list g
    ^ Etc.tabs i ^ string_of_rule_type rt (* TODO: check that this prints the rule_type correctly *)
    ^ (if List.is_empty rcs then "" (* TODO: check that this prints the rule_constr list correctly *)
      else Etc.tabs i ^ (string_of_rule_constrs rcs))
  in
  let string_of_cons_rule verb f p g =
    Etc.tabs i     ^ "whenever" ^ string_of_epattern p ^ "\n"
    ^ string_of_formula_list f  ^ Etc.tabs i   ^ verb  ^ "\n"
    ^ string_of_formula_list g
  in
  let string_of_ref_rule verb f p refs =
    Etc.tabs i     ^ "whenever" ^ string_of_epattern p ^ "\n"
    ^ string_of_formula_list f                         ^ "\n"
    ^ Etc.tabs i   ^ verb                              ^ "\n"
    ^ string_of_reference_list refs
  in
  let string_of_refc_rule verb f p refs g =
    Etc.tabs i     ^ "whenever"  ^ string_of_epattern p ^ "\n"
    ^ string_of_formula_list f                          
    ^ Etc.tabs i   ^ verb                               ^ "\n"
    ^ string_of_reference_list refs                     
    ^ Etc.tabs i   ^ "constitute"                       ^ "\n"
    ^ string_of_formula_list g
  in
  match erule with
  | EObligation _ ->
    let f, p, g, q, rt, rcs = get_obligation_params compilation_rules erule in
    string_of_imp_rule (verb_of_erule erule) f p g q rcs rt
  | EPermission _ ->
    let f, p, g, q, rt, rcs = get_obligation_params compilation_rules erule in
    string_of_imp_rule (verb_of_erule erule) f p g q rcs rt
  | EConstitutive _ ->
    let f, p, g = get_constitutive_params compilation_rules erule in
    string_of_cons_rule (verb_of_erule erule) f p g
  | EException _ ->
    let f, p, erefs = get_exception_params compilation_rules erule in
    string_of_ref_rule (verb_of_erule erule) f p (List.map ~f:(fun (_,_,x) -> x) erefs)
  | EExceptionC _ ->
    let f, p, erefs, g = get_exceptionc_params compilation_rules erule in
    string_of_refc_rule (verb_of_erule erule) f p (List.map ~f:(fun (_,_,x) -> x) erefs) g
  | EScope _ ->
    let f, p, erefs = get_exception_params compilation_rules erule in
    string_of_ref_rule (verb_of_erule erule) f p (List.map ~f:(fun (_,_,x) -> x) erefs)

let string_of_estmt compilation_rules ?(i=0) =
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
        (string_of_erule compilation_rules (i+1) rule)
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
  String.concat ~sep:"\n" (List.map eprog.estmts ~f:(string_of_estmt eprog.compilation_rules))

let print_eprog eprog =
  Stdio.printf "%s\n" (string_of_eprog eprog)
