open Core

module Patt = Pattern

open Lex

module Zinterval = MFOTL_lib.Zinterval

(* Typing context *)

type ctxt = TypeTerm.ctxt

(* Imports *)

type 'a tannot =
  | TALex of 'a
  | TAFormex of string * 'a

let of_annot = function
  | TALex x -> x
  | TAFormex (_, x) -> x

(* References to a section / rule *)

module Ref = struct

  type t = { sks:   (section_kind * ident) list;
             rule:  ident option;
             label: Label.t;
             pos:   LexingInfo.t }

  let make sks rule label pos = { sks; rule; label; pos }

  let from_lex_ref (ref: Lex.Ref.t) label =
    make ref.sks ref.rule label ref.pos

  let to_string (ref : t) =
    let rule_id = match ref.rule with
      | Some r -> " rule \"" ^ r ^ "\""
      | None ->  "" in 
    let string_of_section_kind_and_name (s, n) =
      string_of_section_kind s ^ " \"" ^ n ^ "\"" in
    String.concat ~sep:" " (List.map ~f:string_of_section_kind_and_name ref.sks) ^ rule_id 

  let to_lex_ref (ref: t) : Lex.Ref.t =
    Lex.Ref.make ref.sks ref.rule ref.pos
    
  let to_rtref_expr (ref_expr: t) =
    Label.RuleTree.{label = ref_expr.label; ref = to_lex_ref ref_expr; pos = ref_expr.pos}

end

(* Temporal patterns *)

module Pattern = Patt.Make(Tformula.Info)(Term.StringVar)(Dom)(TTerm)

(* Rule declarations *)

type trule =
  | TObligation   of LexingInfo.t * Pattern.t * Pattern.t * rule_type * rule_constr list
  | TPermission   of LexingInfo.t * Pattern.t * Pattern.t * rule_type * rule_constr list
  | TConstitutive of LexingInfo.t * Pattern.t * Tformula.t list
  | TException    of LexingInfo.t * Pattern.t * Ref.t list * Tformula.t
  | TExceptionC   of LexingInfo.t * Pattern.t * Ref.t list * Tformula.t * Tformula.t list
  | TScope        of LexingInfo.t * Pattern.t * Ref.t list * Tformula.t

type trule_type =
  | TRTObligation
  | TRTPermission
  | TRTConstitutive
  | TRTException
  | TRTExceptionC
  | TRTScope

type tdisjunct = {
  rule_id:         int;
  rule_type:       trule_type;
  rule_pos:        LexingInfo.t;
  def_pos:         LexingInfo.t;
  pf:              Pattern.t;
  exceptions:      Tformula.t list;                                   (* list of predicates *)
  scopes:          Tformula.t list;                                   (* list of predicates *)
  fv_renaming:     (string, string, String.comparator_witness) Map.t; (* renaming of free variables *)
  params_original: TTerm.t list;                                      (* list of the original terms *)
  params_new:      TTerm.t list;                                      (* list of the new terms *)
}

type tcrule =
  | TCImplication   of int * trule_type * LexingInfo.t * Pattern.t * Tformula.t list * Tformula.t list * Pattern.t * rule_type * rule_constr list
  | TCDefinitionRef of int * trule_type * LexingInfo.t * Pattern.t * Tformula.t list * Tformula.t list * Ref.t list * Tformula.t
  | TCDefinitionDis of (int, tdisjunct, Int.comparator_witness) Map.t * Tformula.t

let pos_of_tcrule = function
  | TCImplication (_, _, pos, _, _, _, _, _, _) -> pos
  | TCDefinitionRef (_, _, pos, _, _, _, _, _) -> pos
  | TCDefinitionDis (m, _) -> LexingInfo.union_all (List.map (Map.data m) ~f:(fun disjunct -> disjunct.rule_pos))

(* Statements and programs *)

type tstmt =
  | TSImport   of LexingInfo.t * string list * import_format
  | TSSection  of section_kind * Label.t * string * string tannot option
  | TSRule     of LexingInfo.t * int * Label.t * (ident * TypeTerm.t) list * trule * string tannot option
  | TSEvent    of event_type * ident * (ident * TypeTerm.t) list * (Enftype.t * bool) * string option
  | TSType     of ident * TypeTerm.t option * string option
  | TSFunction of ident * (ident * TypeTerm.t) list * TypeTerm.t * string option
  | TSNote     of string

type tevent = event_type * (ident * TypeTerm.t) list * (Enftype.t * bool) * string option
type tfunction = (ident * TypeTerm.t) list * TypeTerm.t * string option
type var_types = (ident, TypeTerm.t, Base.String.comparator_witness) Map.t

type tprog =
  {
    tstmts:               tstmt list;
    taliases:             (ident, TypeTerm.t option * string option, Base.String.comparator_witness) Map.t;
    (* maps type aliases to their underlying type *)
    tsubtypes:            (ident, TypeTerm.t, Base.String.comparator_witness) Map.t;
    (* maps subtypes to their supertypes *)
    tevents:              (ident, tevent, Base.String.comparator_witness) Map.t;
    (* maps event names to their definitions *)
    tfunctions:           (ident, tfunction, Base.String.comparator_witness) Map.t;
    (* maps function names to their definitions *)
    rule_ctxts:           (int, ctxt, Int.comparator_witness) Map.t;
    (* maps rule labels to variables used in section *)
    rule_tree:            Label.RuleTree.s;
    exception_predicates: (int, Tformula.t, Int.comparator_witness) Map.t;
    scope_predicates:     (int, Tformula.t, Int.comparator_witness) Map.t;
  }

let tempty =
  {
    tstmts               = [];
    taliases             = Map.empty (module String);
    tsubtypes            = Map.empty (module String);
    tevents              = Builtin.events_map;
    tfunctions           = Builtin.functions_map;
    rule_ctxts           = Map.empty (module Int); 
    rule_tree            = Label.RuleTree.empty;
    exception_predicates = Map.empty (module Int);
    scope_predicates     = Map.empty (module Int);
  }

(* Functions to extend programs *)

let add_tstmt (tstmt: tstmt) (tprog: tprog) = { tprog with tstmts = tstmt::tprog.tstmts }

let add_talias name typ doc_string tprog pos =
  let open Errors.OrErrors in
  (* TODO: (potentially in the future) allow for overwriting/reusing existing type names *)
  let* aliases =
    try ok (Map.add_exn tprog.taliases ~key:name ~data:(typ, doc_string))
    with _ -> error (Errors.type_error (Printf.sprintf "type alias %s already exists" name) pos)
  in
  ok { tprog with taliases = aliases; tstmts = TSType (name, typ, doc_string)::tprog.tstmts }

let rec check_arg_type tprog pos =
  let open Errors.OrErrors in
  function
  | TypeTerm.TConst tt -> ok (TypeTerm.TConst tt)
  | TNamed tn when Map.mem tprog.taliases tn -> ok (TypeTerm.TNamed tn)
  | TNamed tn ->
     error (Errors.type_error
              (Printf.sprintf "the type %s does not exist" tn) pos)
  | TVar tv -> ok (TypeTerm.TVar tv)
  | TSum kvs ->
     let f (k, v) = let* v = check_arg_type tprog pos v in ok (k, v) in
     let* kvs = all (List.map ~f kvs) in
     ok (TypeTerm.TSum kvs)

let check_arg_types tprog pos args =
  let open Errors.OrErrors in
  let f (arg, ttt) = let* ttt = check_arg_type tprog pos ttt in ok (arg, ttt) in
  let names = List.dedup_and_sort (List.map ~f:fst args) ~compare:String.compare in
  if List.length names = List.length args then
    all (List.map ~f args)
  else
    error (Errors.type_error "duplicate argument names" pos) 
     
let add_tevent event_type name (args : (ident * TypeTerm.t) list) (enftype, itl) ds tprog pos =
  let open Errors.OrErrors in
  let event = (event_type, args, (enftype, itl), ds) in
  let* args = check_arg_types tprog pos args in
  (* TODO: (potentially in the future) allow for overwriting/reusing event names *)
  let* events =
    try ok (Map.add_exn tprog.tevents ~key:name ~data:event)
    with _ -> error (Errors.type_error (Printf.sprintf "event %s already exists" name) pos)
  in
  ok { tprog with tevents = events; tstmts = TSEvent (event_type, name, args, (enftype, itl), ds)::tprog.tstmts}

let add_tfunction name arg_types return_type ds tprog pos =
  let open Errors.OrErrors in
  let function_ = (arg_types, return_type, ds) in
  (* TODO: allow for overwriting/reusing event names *)
  let* arg_types = check_arg_types tprog pos arg_types in
  let* return_type = check_arg_type tprog pos return_type in
  let* functions =
    try ok (Map.add_exn tprog.tfunctions ~key:name ~data:function_)
    with _ -> error (Errors.type_error (Printf.sprintf "function %s already exists" name) pos)
  in
  ok { tprog with tfunctions = functions; tstmts = TSFunction (name, arg_types, return_type, ds)::tprog.tstmts}
  
let add_exception i f (trefs: Ref.t list) tprog =
  let open Errors.OrErrors in
  let* rule_tree = Label.RuleTree.add_exception i (List.map ~f:Ref.to_rtref_expr trefs) tprog.rule_tree in
  ok { tprog with exception_predicates = Map.add_exn tprog.exception_predicates ~key:i ~data:f; rule_tree }

let add_scope i f (trefs: Ref.t list) tprog =
  let open Errors.OrErrors in
  let* rule_tree = Label.RuleTree.add_scope i (List.map ~f:Ref.to_rtref_expr trefs) tprog.rule_tree in
  ok { tprog with scope_predicates = Map.add_exn tprog.scope_predicates ~key:i ~data:f; rule_tree }

let set_labels pos label tprog =
  { tprog with rule_tree = Label.RuleTree.add_label pos tprog.rule_tree label }

let label_of_rule tprog id = Map.find_exn tprog.rule_tree.label_of_rule id

let add_vars id vs tprog =
  let rule_ctxts = try Map.add_exn tprog.rule_ctxts ~key:id ~data:vs
                   with _ -> assert false
  in { tprog with rule_ctxts }

let add_rule pos rule_num label tprog =
  let open Errors.OrErrors in
  let* rule_tree = Label.RuleTree.add_rule pos rule_num label tprog.rule_tree in
  ok { tprog with rule_tree }

let add_section pos label tprog =
  let open Errors.OrErrors in
  ok { tprog with rule_tree = Label.RuleTree.add_section pos label tprog.rule_tree }

let find_rule_statement_by_id (tprog: tprog) (id: int) : tstmt Errors.OrErrors.t =
  let open Errors.OrErrors in
  let rule = List.find tprog.tstmts ~f:(function
      | TSRule (_, i, _, _, _, _) -> Int.equal i id
      | _ -> false) in
  match rule with
  | Some r -> ok r
  | None -> error (Errors.type_error (Printf.sprintf "rule with id %d not found" id) LexingInfo.dummy)

let find_trule_by_id (tprog: tprog) (id: int) : trule Errors.OrErrors.t =
  let open Errors.OrErrors in
  let* tstmt = find_rule_statement_by_id tprog id in
  match tstmt with
  | TSRule (_, _, _, _, trule, _) -> ok trule
  | _ -> assert false

(* Signature *)

module Sig = struct

  type term

  type pred_kind = Trace | Predicate | External | Builtin | Let
                   [@@deriving compare, sexp_of, hash, equal]

  let prog = ref tempty

  let set_prog p = prog := p
  
  let rank_of_pred p_name =
    let _, args, _, _ = Map.find_exn !prog.tevents p_name in
    List.length args
  
  let mem p_name =
    Map.mem !prog.tevents p_name

  let enftype_of_pred p_name =
    let _, _, (enftype, _), _ = Map.find_exn !prog.tevents p_name in
    (*Stdio.printf "Tlex.Sig.enftype_of_pred (%s) = %s\n" p_name (Enftype.to_string enftype);*)
    enftype

  let kind_of_pred p_name =
    let event_type, _, _, _ = Map.find_exn !prog.tevents p_name in
    match event_type with
    | Event _  | Exception -> Trace
    | Predicate -> Predicate


  let pred_enftype_map () =
    Map.map !prog.tevents
      ~f:(fun data -> let _, args, (enftype, _), _ = data in
                      (enftype, List.init (List.length args) ~f:(fun x -> x)))

  let strict_of_func _ = false
  
  let add_letpred_empty _ = assert false
  
  let update_enftype p_name enftype =
    prog := {
        !prog with
        tevents = Map.update !prog.tevents p_name
                    ~f:(function
                      | Some data -> let event_type, args, (_, itl), ds = data in
                                     (event_type, args, (enftype, itl), ds)
                      | None -> assert false)
      }

end

(* Printing functions *)

let verb_of_trule = function
  | TObligation _ -> "oblige"
  | TPermission _ -> "permit"
  | TConstitutive _ -> "constitute"
  | TException _
    | TExceptionC _ -> "except"
  | TScope _ -> "scope"

let string_of_trule i trule =
  let open Pattern in
  let to_string f = Util.tabs (i+1) ^ Tformula.to_string f in
  let ref_to_string r = Util.tabs (i+1) ^ Lex.Ref.to_string r in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:to_string f) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Util.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_imp_rule verb fp1 fp2 rcs rt =
    Util.tabs i     ^ "whenever" ^ Pattern.patt_to_string fp1.patt ^ "\n"
    ^ string_of_formula_list fp1.fs
    ^ Util.tabs i   ^ verb     ^ Pattern.patt_to_string fp2.patt ^ "\n"
    ^ string_of_formula_list fp2.fs
    ^ Util.tabs i ^ string_of_rule_type rt (* TODO: check that this prints the rule_type correctly *)
    ^ (if List.is_empty rcs then "" (* TODO: check that this prints the rule_constr list correctly *)
      else Util.tabs i ^ (string_of_rule_constrs rcs))
  in
  let string_of_cons_rule verb fp g =
    Util.tabs i     ^ "whenever" ^ Pattern.patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs
    ^ Util.tabs i   ^ verb      ^ "\n"
    ^ string_of_formula_list g
  in
  let string_of_ref_rule verb fp refs =
    (* let refs = List.map trefs ~f:Label.reference_of_label in *)
    Util.tabs i     ^ "whenever" ^ Pattern.patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs
    ^ Util.tabs i   ^ verb                             ^ "\n"
    ^ String.concat ~sep:"\n" (List.map refs ~f:ref_to_string)
  in
  let string_of_refc_rule verb fp refs g =
    Util.tabs i     ^ "whenever"  ^ Pattern.patt_to_string fp.patt ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Util.tabs i   ^ verb
    ^ String.concat ~sep:"\n" (List.map refs ~f:ref_to_string)
    ^ Util.tabs i   ^ "constitute"
    ^ string_of_formula_list g
  in
  match trule with
  | TObligation (_, fp1, fp2, rt, rcs)
  | TPermission (_, fp1, fp2, rt, rcs)
    -> string_of_imp_rule (verb_of_trule trule) fp1 fp2 rcs rt
  | TConstitutive (_, fp, g)
    -> string_of_cons_rule (verb_of_trule trule) fp g
  | TException (_, fp, trefs, _)
  | TScope (_, fp, trefs, _)
    -> string_of_ref_rule (verb_of_trule trule) fp (List.map ~f:Ref.to_lex_ref trefs)
  | TExceptionC (_, fp, trefs, _, g)
    -> string_of_refc_rule (verb_of_trule trule) fp (List.map ~f:Ref.to_lex_ref trefs) g

let string_of_tstmt ?(i=0) =
  function
  | TSImport (_, idents, _) ->
     Printf.sprintf "import %s"
       (String.concat ~sep:"." idents)
  | TSSection (section_kind, _, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Util.tabs i)
       (string_of_section_kind section_kind)
       label
       (match title with Some title -> Printf.sprintf ": \"%s\"" (of_annot title) | None -> "")
  | TSRule (_, _, label, type_fixes, rule, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string (of_annot s) i
          | None -> ""
      in
      Printf.sprintf "%srule %s\n%s%s%s"
        (Util.tabs i)
        (Label.qualified_name label)
        (string_of_type_fixes (i+1) type_fixes)
        (string_of_trule (i+1) rule)
        description
  | TSEvent (event_type, name, typed_args, (enftype, itl), doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
      Printf.sprintf "%s%s%s %s %s\n%s%s"
          (Util.tabs i)
          (Enftype.to_string enftype)
          (if itl then " internal" else "")
          (string_of_event_type event_type)
          name
          description
          (string_of_args typed_args i)
  | TSType (name, typ, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> "" in
      let typ_string =
       match typ with
       | Some tt -> " is " ^ TypeTerm.to_string tt
       | None -> "" in
     Printf.sprintf "%stype %s%s%s"
       (Util.tabs i) name typ_string description
  | TSFunction (name, typed_args, return_typ, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string s i
          | None -> ""
     in
     let f (ident, typ) =
       Printf.sprintf "%s : %s" ident (TypeTerm.to_string typ) in
     Printf.sprintf "%sfunction %s(%s) -> %s%s"
       (Util.tabs i)
       name
       (String.concat ~sep:", " (List.map typed_args ~f))
       (TypeTerm.to_string return_typ)
       description
  | TSNote text -> "note \"" ^ text ^ "\""

let string_of_signature signature =
  match signature with
  | name, typed_idents ->
     Printf.sprintf "%s(%s)"
       name
       (String.concat ~sep:", " (List.map typed_idents ~f:string_of_typed_idents))
    
let string_of_tprog tprog =
  String.concat ~sep:"\n\n" (List.map tprog.tstmts ~f:string_of_tstmt)

let print_tprog tprog =
  Stdio.printf "%s\n" (string_of_tprog tprog)
