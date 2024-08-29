open Core
open Lex

type tpattern =
  | TPPresent
  | TPEventually of Interval.t
  | TPAlways of Interval.t
  | TPUntil of Interval.t * Tformula.t
  | TPOnce of Interval.t
  | TPHistorically of Interval.t
  | TPSince of Interval.t * Tformula.t

let tpattern_to_string = function
  | TPPresent -> ""
  | TPEventually i -> Printf.sprintf "◊%s" (Interval.to_string i)
  | TPAlways i -> Printf.sprintf "□%s" (Interval.to_string i) 
  | TPUntil (i, f) -> Printf.sprintf "%s U%s" (Tformula.to_string f) (Interval.to_string i)
  | TPOnce i -> Printf.sprintf "⧫%s" (Interval.to_string i)
  | TPHistorically i -> Printf.sprintf "■%s" (Interval.to_string i)
  | TPSince (i, f) -> Printf.sprintf "%s S%s" (Tformula.to_string f) (Interval.to_string i)

type tref_expr = {
  label: Label.t;
  ref: Lex.reference;
  pos: Lexing.position
}
let to_rtref_expr (tref: tref_expr) = Label.RuleTree.{label = tref.label; ref = tref.ref; pos = tref.pos}

let make_tref_expr pos label sks rule = { label; ref = Lex.make_reference sks rule; pos }

type tpformula = {p: tpattern; fs: Tformula.t list}

let tpf p fs = {p; fs}

let tpformula_to_string tpf =
  Printf.sprintf "{p = %s; fs = [%s]}"
    (tpattern_to_string tpf.p)
    (String.concat ~sep:", " (List.map tpf.fs ~f:Tformula.to_string))

type trule =
  | TObligation   of Lexing.position * tpformula * tpformula * rule_type * rule_constr list
  | TPermission   of Lexing.position * tpformula * tpformula * rule_type * rule_constr list
  | TConstitutive of Lexing.position * tpformula * Tformula.t list
  | TException    of Lexing.position * tpformula * tref_expr list * Tformula.t
  | TExceptionC   of Lexing.position * tpformula * tref_expr list * Tformula.t * Tformula.t list
  | TScope        of Lexing.position * tpformula * tref_expr list * Tformula.t

type trule_type = TRTObligation | TRTPermission | TRTConstitutive | TRTException | TRTExceptionC | TRTScope

type tdisjunct = {
  rule_id: int;
  tt: trule_type;
  rule_pos: Lexing.position;
  def_positions: Lexing.position list;
  pf: tpformula;
  exceptions: Tformula.t list; (* list of predicate *)
  scopes: Tformula.t list; (* list of predicate *)
  fv_renaming: (string, string, String.comparator_witness) Map.t; (* renaming of free variables *)
  params_original: Tformula.TTerm.t list; (* list of the original terms*)
  params_new: Tformula.TTerm.t list; (* list of the new terms *)
}

type tcrule =
  | TCImplication   of int * trule_type * Lexing.position * tpformula * Tformula.t list * Tformula.t list * tpformula * rule_type * rule_constr list
  | TCDefinition    of int * trule_type * Lexing.position * tpformula * Tformula.t list * Tformula.t list * tref_expr list * Tformula.t
  | TCDefinitionDis of (int, tdisjunct, Int.comparator_witness) Map.t * Tformula.t

type 'a tannot =
  | TALex of 'a
  | TAFormex of string * 'a

let of_annot = function
  | TALex x -> x
  | TAFormex (_, x) -> x

type tstmt =
  | TSImport  of Lexing.position * string list * import_format
  | TSSection of section_kind * Label.t * string * string tannot option
  | TSRule    of Lexing.position * int * Label.t * (ident * Formula.TypeTerm.t) list * trule * string tannot option
  | TSEvent   of event_type * ident * (Lexing.position * ident * Formula.TypeTerm.t) list * pol * string option
  | TSType    of ident * Formula.TypeTerm.t option * string option
  | TSFunction of ident * (ident * Formula.TypeTerm.t) list * Formula.TypeTerm.t * string option
  | TSNote    of string

type tevent = event_type * (Lexing.position * ident * Formula.TypeTerm.t) list * pol * string option
type tfunction = (ident * Formula.TypeTerm.t) list * Formula.TypeTerm.t * string option

type var_types = (ident, Formula.TypeTerm.t, Base.String.comparator_witness) Map.t

type tprog =
  {
    tstmts: tstmt list;
    taliases: (ident, Formula.TypeTerm.t option * string option, Base.String.comparator_witness) Map.t;
    (* maps type aliases to their underlying type *)
    tevents: (ident, tevent, Base.String.comparator_witness) Map.t;
    (* maps event names to their definitions *)
    tfunctions: (ident, tfunction, Base.String.comparator_witness) Map.t;
    (* maps function names to their definitions *)
    variables: (int, var_types, Int.comparator_witness) Map.t;
    (* maps rule labels to variables used in section *)
    rule_tree: Label.RuleTree.s;
    exception_predicates: (int, Tformula.t, Int.comparator_witness) Map.t;
    scope_predicates: (int, Tformula.t, Int.comparator_witness) Map.t;
  }

let tempty =
  {
    tstmts = [];
    taliases = Map.empty (module String);
    tevents = Builtin.events_map;
    tfunctions = Builtin.functions_map;
    variables = Map.empty (module Int); 
    rule_tree = Label.RuleTree.empty;
    exception_predicates = Map.empty (module Int);
    scope_predicates = Map.empty (module Int);
  }

let formulas_from_tpattern = function
  | TPPresent
  | TPEventually _
  | TPAlways _
  | TPOnce _
  | TPHistorically _ -> []
  | TPUntil (_, f) 
  | TPSince (_, f) -> [f]

let fv_of_tpattern ?(map=Map.empty (module String)) = function
  | TPPresent
  | TPEventually _
  | TPOnce _
  | TPAlways _
  | TPHistorically _ -> map
  | TPUntil (_, f)
  | TPSince (_, f) -> Tformula.fv ~map f

let fv_of_tpformula ?(map=Map.empty (module String)) {p; fs} =
  List.fold fs ~init:(fv_of_tpattern ~map p)
    ~f:(fun acc f -> Tformula.fv ~map:acc f)

let trule_map tprog =
  List.fold tprog.tstmts ~init:(Map.empty (module Int))
    ~f:(fun acc -> function
        | TSRule (_, i, _, _, rule, _) -> Map.add_exn acc ~key:i ~data:rule
        | _ -> acc)

let pol_map tprog =
  Map.map tprog.tevents ~f:(fun (_, _, pol, _) -> pol)

let add_tstmt tstmt tprog = { tprog with tstmts = tstmt::tprog.tstmts }

let add_talias name typ doc_string tprog pos =
  (* TODO: (potentially in the future) allow for overwriting/reusing existing type names *)
  let aliases =
    try Map.add_exn tprog.taliases ~key:name ~data:(typ, doc_string)
    with _ -> Util.type_error (Printf.sprintf "type alias %s already exists" name) [pos]
  in
  { tprog with taliases = aliases; tstmts = TSType (name, typ, doc_string)::tprog.tstmts }

let add_tevent event_type name args pol ds tprog pos =
  let event = (event_type, args, pol, ds) in
  (* TODO: (potentially in the future) allow for overwriting/reusing event names *)
  let events =
    try Map.add_exn tprog.tevents ~key:name ~data:event
    with _ -> Util.type_error (Printf.sprintf "event %s already exists" name) [pos]
  in
  { tprog with tevents = events; tstmts = TSEvent (event_type, name, args, pol, ds)::tprog.tstmts}

let add_tfunction name arg_types return_type ds tprog pos =
  let function_ = (arg_types, return_type, ds) in
  (* TODO: allow for overwriting/reusing event names *)
  let functions =
    try Map.add_exn tprog.tfunctions ~key:name ~data:function_
    with _ -> Util.type_error (Printf.sprintf "function %s already exists" name) [pos]
  in
  { tprog with tfunctions = functions; tstmts = TSFunction (name, arg_types, return_type, ds)::tprog.tstmts}

(*let add_vars vs name tprog pos =
  let variables =
    try Map.add_exn tprog.variables ~key:name ~data:vs
    with _ -> let err_msg = Printf.sprintf
                "rule label '%s' has already been defined"
                name in
      Util.label_error err_msg pos
  in
  { tprog with variables = variables }*)

let add_exception i f (trefs: tref_expr list) tprog =
  { tprog with exception_predicates = Map.add_exn tprog.exception_predicates ~key:i ~data:f;
               rule_tree = Label.RuleTree.add_exception i (List.map ~f:to_rtref_expr trefs) tprog.rule_tree }

let add_scope i f (trefs: tref_expr list) tprog =
  { tprog with scope_predicates = Map.add_exn tprog.scope_predicates ~key:i ~data:f;
               rule_tree = Label.RuleTree.add_scope i (List.map ~f:to_rtref_expr trefs) tprog.rule_tree }

let set_labels pos label tprog =
  { tprog with rule_tree = Label.RuleTree.add_label pos tprog.rule_tree label }

let label_of_rule tprog id = Map.find_exn tprog.rule_tree.label_of_rule id

let add_vars id vs tprog =
  let variables = try Map.add_exn tprog.variables ~key:id ~data:vs
    with _ -> assert false
  in { tprog with variables = variables }

let add_rule pos rule_num label tprog =
  { tprog with rule_tree = Label.RuleTree.add_rule pos rule_num label tprog.rule_tree }

let add_section pos label tprog =
  { tprog with rule_tree = Label.RuleTree.add_section pos label tprog.rule_tree }


let is_trule = function
  | TSRule _ -> true
  | _ -> false

let verb_of_trule = function
  | TObligation _ -> "oblige"
  | TPermission _ -> "permit"
  | TConstitutive _ -> "constitute"
  | TException _
    | TExceptionC _ -> "except"
  | TScope _ -> "scope"


let string_of_tpattern = function
  | TPPresent -> ""
  | TPEventually i -> " eventually " ^ Interval.to_string i 
  | TPAlways i -> " always in the future " ^ Interval.to_string i 
  | TPUntil (i, f) -> " eventually delaying if " ^ Tformula.to_string f ^ " " ^ Interval.to_string i
  | TPOnce i -> " once " ^ Interval.to_string i
  | TPHistorically i -> " always in the past " ^ Interval.to_string i
  | TPSince (i, f) -> " always since " ^ Tformula.to_string f ^ " " ^ Interval.to_string i

let predicates_of_tpattern = function
  | TPPresent
  | TPEventually _
  | TPAlways _
  | TPHistorically _
    | TPOnce _ -> []
  | TPUntil (_, f)
    | TPSince (_, f) -> Tformula.collect_tpredicates [] f

let string_of_trule i trule =
  let to_string f = Etc.tabs (i+1) ^ Tformula.to_string f in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:to_string f) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Etc.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_imp_rule verb fp1 fp2 rcs rt =
    Etc.tabs i     ^ "whenever" ^ string_of_tpattern fp1.p ^ "\n"
    ^ string_of_formula_list fp1.fs ^ "\n"
    ^ Etc.tabs i   ^ verb     ^ string_of_tpattern fp2.p ^ "\n"
    ^ string_of_formula_list fp2.fs
    ^ Etc.tabs i ^ string_of_rule_type rt (* TODO: check that this prints the rule_type correctly *)
    ^ (if List.is_empty rcs then "" (* TODO: check that this prints the rule_constr list correctly *)
      else Etc.tabs i ^ (string_of_rule_constrs rcs))
  in
  let string_of_cons_rule verb fp g =
    Etc.tabs i     ^ "whenever" ^ string_of_tpattern fp.p ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Etc.tabs i   ^ verb      ^ "\n"
    ^ string_of_formula_list g
  in
  let string_of_ref_rule verb fp refs =
    (* let refs = List.map trefs ~f:Label.reference_of_label in *)
    Etc.tabs i     ^ "whenever" ^ string_of_tpattern fp.p ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Etc.tabs i   ^ verb                             ^ "\n"
    ^ String.concat ~sep:"\n" (List.map refs ~f:Lex.string_of_reference)
  in
  let string_of_refc_rule verb fp refs g =
    Etc.tabs i     ^ "whenever"  ^ string_of_tpattern fp.p ^ "\n"
    ^ string_of_formula_list fp.fs ^ "\n"
    ^ Etc.tabs i   ^ verb
    ^ String.concat ~sep:"\n" (List.map refs ~f:Lex.string_of_reference)
    ^ Etc.tabs i   ^ "constitute"
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
    -> string_of_ref_rule (verb_of_trule trule) fp (List.map ~f:(fun tref -> tref.ref) trefs)
  | TExceptionC (_, fp, trefs, _, g)
    -> string_of_refc_rule (verb_of_trule trule) fp (List.map ~f:(fun tref -> tref.ref) trefs) g

let string_of_tstmt ?(i=0) =
  function
  | TSImport (_, idents, _) ->
     Printf.sprintf "import %s"
       (String.concat ~sep:"." idents)
  | TSSection (section_kind, _, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Etc.tabs i)
       (string_of_section_kind section_kind)
       label
       (match title with Some title -> Printf.sprintf ": \"%s\"" (of_annot title) | None -> "")
  | TSRule (_, _, label, type_fixes, rule, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string (of_annot s) i
          | None -> ""
      in
      Printf.sprintf "%srule%s\n%s%s\n%s"
        (Etc.tabs i)
        (Label.qualified_name label)
        (string_of_type_fixes (i+1) type_fixes)
        (string_of_trule (i+1) rule)
       description
  | TSEvent (event_type, name, typed_args, pol, doc_string) ->
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
  | TSType (name, typ, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> "" in
      let typ_string =
       match typ with
       | Some tt -> " is " ^ Formula.TypeTerm.value_to_string tt
       | None -> "" in
     Printf.sprintf "%stype %s%s%s"
       (Etc.tabs i) name typ_string description
  | TSFunction (name, typed_args, return_typ, doc_string) ->
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
  | TSNote text -> "note \"" ^ text ^ "\""

let string_of_signature signature =
  match signature with
  | name, typed_idents ->
     Printf.sprintf "%s(%s)"
       name
       (String.concat ~sep:", " (List.map typed_idents ~f:string_of_typed_idents))
    
let string_of_tprog tprog =
  String.concat ~sep:"\n" (List.map tprog.tstmts ~f:string_of_tstmt)

let string_of_var_types var_types =
  let f (k, v) = k ^ " : " ^ Formula.TypeTerm.to_string v in
  "[" ^ String.concat ~sep:", " (List.map (Map.to_alist var_types) ~f) ^ "]"

let print_tprog tprog =
  Stdio.printf "%s\n" (string_of_tprog tprog)


let unpack_functional tevents trm' trm =
  match Tformula.TTerm.(trm.trm) with
  | Tformula.TTerm.TApp (f, trms) ->
     (match Map.find tevents f with
      | Some (Event (_, Functional), _, _, _) ->
         Some (f, trms @ [trm'])
      | _ -> None)
  | _ -> None

let unpack_variable tevents trm' trm =
  match Tformula.TTerm.(trm.trm) with
  | Tformula.TTerm.TVar x ->
     (match Map.find tevents x with
      | Some (Event (_, Variable), _, _, _) ->
         Some (x, [trm'])
      | _ -> None)
  | _ -> None

let unpack_special_eq tevents trm trm' =
  List.find_map
    [unpack_functional tevents trm trm';
     unpack_functional tevents trm' trm;
     unpack_variable tevents trm trm';
     unpack_variable tevents trm' trm]
    ~f:(fun x -> x)

let strict_of_tformulas stricts itv fut fs =
  List.for_all fs ~f:(Tformula.strict ~itl_strict:stricts ~itv:itv ~fut:fut)

let strict_of_tpformula stricts (tpf: tpformula) =
  match tpf.p with
  | TPPresent -> strict_of_tformulas stricts (Zinterval.singleton 0) false tpf.fs
  | TPEventually i
    | TPAlways i -> strict_of_tformulas stricts (Zinterval.of_interval i) true tpf.fs
  | TPOnce i
    | TPHistorically i -> strict_of_tformulas stricts (Zinterval.inv (Zinterval.of_interval i)) false tpf.fs
  | TPUntil (i, g) -> (strict_of_tformulas stricts (Zinterval.inv (Zinterval.of_interval i)) true tpf.fs)
                      || (Tformula.strict ~itl_strict:stricts ~itv:(Zinterval.inv (Zinterval.of_interval i)) ~fut:true g)
  | TPSince (i, g) -> (strict_of_tformulas stricts (Zinterval.inv (Zinterval.of_interval i)) false tpf.fs)
                      || (Tformula.strict ~itl_strict:stricts ~itv:(Zinterval.inv (Zinterval.of_interval i)) ~fut:false g)

let relative_interval_of_tpformula itvls (tpf: tpformula) =
  let j =
    let aux f = Tformula.relative_interval ~itl_itvs:itvls f in
    Zinterval.lubs (List.map tpf.fs ~f:aux)
  in
  match tpf.p with
  | TPPresent -> j
  | TPEventually i
  | TPAlways i ->
    let i = Zinterval.of_interval i in
    Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
  | TPOnce i
  | TPHistorically i ->
    let i = Zinterval.of_interval i |> Zinterval.inv in
    Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
  | TPUntil (i, g) ->
    let i = Zinterval.of_interval i in
    let k = Tformula.relative_interval ~itl_itvs:itvls g in
    (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i) k)
      (Zinterval.sum i j))
  | TPSince (i, g) ->
    let i = Zinterval.of_interval i in
    let k = Tformula.relative_interval ~itl_itvs:itvls g in
    (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i) j)
      (Zinterval.sum i k))

let srp_of_tpformula (itvls, stricts) tpf =
  (Zinterval.is_nonpositive (relative_interval_of_tpformula itvls tpf))
  && (strict_of_tpformula stricts tpf)

let fv_of_tformulas ?(map=Map.empty (module String)) fs =
  List.fold fs ~init:map ~f:(fun map f -> Tformula.fv ~map f)

let fv_of_tpformulas ?(map=Map.empty (module String)) ({fs; p}: tpformula) =
  fv_of_tformulas ~map (fs@formulas_from_tpattern p)

let relative_interval_of_tformulas itl_itvs (fs: Tformula.t list): Zinterval.t =
  let itvs = (List.map fs ~f:(Tformula.relative_interval ~itl_itvs:itl_itvs)) in
  List.fold itvs ~init:Zinterval.full ~f:Zinterval.lub

let relative_interval_of_tpformula itl_itvs (tpf: tpformula): Zinterval.t =
  match tpf.p with
  | TPPresent -> relative_interval_of_tformulas itl_itvs tpf.fs
  | TPEventually i
  | TPAlways i ->
    let i = Zinterval.of_interval i in
    let j = relative_interval_of_tformulas itl_itvs tpf.fs in
    Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
  | TPUntil (i, g) ->
    let i = Zinterval.of_interval i in
    let j = relative_interval_of_tformulas itl_itvs tpf.fs in
    Zinterval.lub 
      (Zinterval.sum (Zinterval.to_zero i) (Tformula.relative_interval ~itl_itvs:itl_itvs g))
      (Zinterval.sum i j)
  | TPOnce i
  | TPHistorically i ->
    let i = Zinterval.of_interval i in
    let j = relative_interval_of_tformulas itl_itvs tpf.fs in
    Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
  | TPSince (i, g) ->
    let i = Zinterval.of_interval i in
    let j = relative_interval_of_tformulas itl_itvs tpf.fs in
    Zinterval.lub
      (Zinterval.sum (Zinterval.to_zero i) j)
      (Zinterval.sum i (Tformula.relative_interval ~itl_itvs:itl_itvs g))

let strict_of_tformulas itl_strict (fs: Tformula.t list) =
  List.for_all fs ~f:(Tformula.strict ~itl_strict:itl_strict)

let strict_of_tpformula itl_strict (tpf: tpformula): bool =
  match tpf.p with
  | TPPresent -> strict_of_tformulas itl_strict tpf.fs
  | TPEventually i
  | TPAlways i ->
    let i = Zinterval.of_interval i in
    not (Zinterval.mem 0 i)
    && strict_of_tformulas itl_strict tpf.fs
  | TPUntil (i, g) ->
    let i = Zinterval.of_interval i in
    not (Zinterval.mem 0 (Zinterval.inv i))
    && strict_of_tformulas itl_strict tpf.fs
    && Tformula.strict ~itl_strict:itl_strict g
  | TPOnce _
  | TPHistorically _ -> strict_of_tformulas itl_strict tpf.fs
  | TPSince (_, g) ->
    strict_of_tformulas itl_strict tpf.fs
    && Tformula.strict ~itl_strict:itl_strict g
