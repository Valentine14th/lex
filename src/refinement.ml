open Core
open Tlex
open Trex
open Erex

module Interval = MFOTL_lib.Interval
module Enftype = MFOTL_lib.Enftype

let debug_refinement = ref true
let debug msg = if !debug_refinement then Errors.debug_print ~f_name:(Some "refinement.ml") msg

(* Visitors *)

let type_trrule : trrule -> errule = function
  | TRefine (pos', pf, g) -> ERefine (pos', Elex.epf_of_tpf pf, Eformula.of_tformulas g)

let type_estmt erule_map : trtmt -> ertmt = function
  | TRStmt tstmt ->
     ERStmt (Enforceability.type_tstmt erule_map tstmt)
  | TRRule (pos, i, label, type_fixes, trrule, doc_string) ->
     ERRule (pos, i, label, type_fixes, type_trrule trrule, doc_string)
  | TRType (pos, name, typ, doc_string) ->
     ERType (pos, name, typ, doc_string)
  | TRReplace (pos, kind, refs1, refs2, doc_string) ->
     ERReplace (pos, kind, refs1, refs2, doc_string)
  | TRAssume (pos, name, b, doc_string) ->
     ERAssume (pos, name, b, doc_string)

let insert_refinement_rules (trefi: trefi) (tprog: tprog) : tprog Errors.OrErrors.t =
  let open Errors.OrErrors in
  let variables  = List.fold_left trefi.trvars_to_add
                     ~init:tprog.variables
                     ~f:(fun m (key, data) -> Map.add_exn m ~key ~data) in
  let* rule_tree = fold_best_effort trefi.trrules_to_add
                     ~init:tprog.rule_tree
                     ~f:(fun s (pos, ri, label) -> Label.RuleTree.add_rule pos ri label s) in
  let tstmts     = trefi.tprog.tstmts @ trefi.trstmts_to_add in
  ok { trefi.tprog with variables; rule_tree; tstmts }
  
let update_types (trefi: trefi) (tprog: tprog) : tprog =
  let f ~key ~data taliases = Map.update taliases key ~f:(fun _ -> data) in
  let taliases = Map.fold trefi.traliases ~init:tprog.taliases ~f in
  { tprog with taliases }

let insert_assumed_event_rules (trefi: trefi) (tprog: tprog) : tprog =
  let make_tsrule b (pos, name, label) =
    let (_, vars, _, _) = Map.find_exn tprog.tevents name in
    let f (x, typ) = Eformula.ETerm.make (Eformula.ETerm.var x) { pos = LexingInfo.dummy; typ } in
    let pred = Tformula.make_dummy (Tformula.Predicate (name, List.map ~f vars)) in
    let idx = Typing.fresh () in
    let fb = if b then Tformula.TT else Tformula.FF in
    let trule = TConstitutive (
                    LexingInfo.dummy,
                    Tlex.Pattern.make PPresent [Tformula.make_dummy fb],
                    [pred]
                  ) in
    TSRule (pos, idx, label, [], trule, None) in
  let f tprog (pos, name, b, label) =
    let tsrule = make_tsrule b (pos, name, label) in
    { tprog with tstmts = tprog.tstmts @ [tsrule] } in
  List.fold_left ~init:tprog ~f trefi.trassumed

let internalize_events (trefi: trefi) (tprog: tprog) : tprog =
  let internalize_event name tprog =
    let update_event (event_type, params, _, doc_string) =
      (event_type, params, Enftype.itl, doc_string) in
    let tevents = 
      Map.update tprog.tevents name
        ~f:(function None -> assert false | Some ev -> update_event ev) in
    { tprog with tevents }
  in List.fold_right ~init:tprog ~f:internalize_event (Set.elements trefi.trrefined)

let replace_rules (trefi: trefi) (tprog: tprog) : tprog Errors.OrErrors.t =
  let open Errors.OrErrors in
  let refs = List.concat_map trefi.trreplacements ~f:(fun (_, _, refs1, _) -> refs1) in
  let rtref_exprs = List.map ~f:Ref.to_rtref_expr refs in
  let* rules_idx_to_replace =
    all (List.map rtref_exprs ~f:(fun ref ->
             Label.RuleTree.find_rules_in_tree ref.pos ref.label tprog.rule_tree.tree))
    >| List.concat in
  let f = function
    | TSRule (_, idx, _, _, _, _) -> not (List.mem rules_idx_to_replace idx ~equal:Int.equal)
    | _ -> true in
  let tstmts = List.filter ~f tprog.tstmts in
  ok { tprog with tstmts }

let replace_inherit_exceptions (trefi: trefi) (tprog: tprog) : tprog Errors.OrErrors.t =
  (* TODO[JD] only inherit exceptions for directly replaced rules, explicitly do not do so for 'new' obligations *)
  let open Errors.OrErrors in
  let tlex_rtref_exprs_to_label_rtref_exprs = List.map ~f:(fun (pos, refs) -> (pos, List.map refs ~f:Ref.to_rtref_expr)) in
  let rules_in_rtref_expr pos (ref: Label.RuleTree.rtref_expr) =
    Label.RuleTree.find_rules_in_tree pos ref.label tprog.rule_tree.tree in
  let rules_in_rtref_exprs ((pos, refs) : (LexingInfo.t * Label.RuleTree.rtref_expr list)) =
    List.map refs ~f:(rules_in_rtref_expr pos)
    |> List.fold_right ~init:(Ok []) ~f:(fun a l -> map2 a l List.append)
  in
  let* rules_refs1 =
    List.map trefi.trreplacements ~f:(fun (pos, _, refs1, _) -> (pos, refs1))
    |> tlex_rtref_exprs_to_label_rtref_exprs
    |> List.map ~f:rules_in_rtref_exprs
    |> all
  in
  let positions = List.map trefi.trreplacements ~f:(fun (pos, _, _, _) -> pos) in
  let check_same_ex_or_sc idx_lists =
    List.map ~f:(List.dedup_and_sort ~compare:Int.compare) idx_lists
    |> List.all_equal ~equal:(fun a b -> Set.equal (Set.of_list (module Int) a) (Set.of_list (module Int) b))
  in
  let option_to_error pos = function
    | Some x -> ok x
    | None -> error (Errors.refinement_error "Rules being replaced must have the same exceptions or scopes, but differ here" pos)
    (* TODO[JD]: maybe allow for differing sets of exceptions across rules being replaced *)
    (* TODO[JD]: display exceptions and rules that differ, replace use of `List.all_equal` with custom function *)
  in
  let ex_or_sc_of_refs map refs =
    List.map refs ~f:(List.map ~f:(Map.find_multi map))
    |> List.map ~f:check_same_ex_or_sc
    |> List.zip_exn positions
    |> List.map ~f:(fun (pos, ex) -> option_to_error pos ex)
    |> all
  in
  let* exceptions_refs1 = ex_or_sc_of_refs tprog.rule_tree.exceptions rules_refs1 in
  let* scopes_refs1 = ex_or_sc_of_refs tprog.rule_tree.scopes rules_refs1 in
  let* rules_refs2 =
    List.map trefi.trreplacements ~f:(fun (pos, _, _, refs2) -> (pos, refs2))
    |> tlex_rtref_exprs_to_label_rtref_exprs
    |> List.map ~f:rules_in_rtref_exprs
    |> all
  in
  let refs1_flat = List.concat rules_refs1 in
  let exceptions_new' : (int, int list, Int.comparator_witness) Map.t =
    List.fold refs1_flat
      ~init:tprog.rule_tree.exceptions
      ~f:(fun exceptions idx -> Map.remove_multi exceptions idx)
  in
  let scopes_new': (int, int list, Int.comparator_witness) Map.t =
    List.fold refs1_flat
      ~init:tprog.rule_tree.scopes
      ~f:(fun scopes idx -> Map.remove_multi scopes idx)
  in
  let refs2_and_ex = List.zip_exn rules_refs2 exceptions_refs1 in
  let refs2_and_sc = List.zip_exn rules_refs2 scopes_refs1 in
  let exceptions: (int, int list, Int.comparator_witness) Map.t =
    List.fold refs2_and_ex ~init:exceptions_new'
      ~f:(fun exceptions (refs2, ex) ->
          List.fold refs2 ~init:exceptions
            ~f:(fun exceptions idx -> Map.add_exn exceptions ~key:idx ~data:ex))
  in
  let scopes: (int, int list, Int.comparator_witness) Map.t =
    List.fold refs2_and_sc ~init:scopes_new'
      ~f:(fun scopes (refs2, ex) ->
          List.fold refs2 ~init:scopes
            ~f:(fun scopes idx -> Map.add_exn scopes ~key:idx ~data:ex))
  in
  ok { tprog with rule_tree = { tprog.rule_tree with exceptions; scopes}}

let hide_and_replace trefi (tprog: tprog) : tprog Errors.OrErrors.t =
  let open Errors.OrErrors in
  ok tprog
  >>= insert_refinement_rules trefi
  >| update_types trefi
  >| insert_assumed_event_rules trefi
  >| internalize_events trefi
  >>= replace_inherit_exceptions trefi
  >>= replace_rules trefi

(* Main typing function *)

let do_type (trefi: Trex.trefi) (b: Interval.v) : Erex.erefi Errors.OrErrors.t =
  let open Errors.OrErrors in
  (* TODO[FH]: check that the refinement is valid *)
  (* TODO[FH]: check that all events have been mapped *)

  let* tprog = hide_and_replace trefi trefi.tprog in
  let* eprog = Enforceability.do_type ~mon_constrs:(trefi.tr_mon, trefi.tr_anti_mon) tprog b in
  let erules = Enforceability.erules_from_tcrules (Enforceability.create_tcrules tprog) in
  ok {
    eprog;
    ertmts = List.map trefi.trtmts ~f:(type_estmt erules);
    lex_file = trefi.lex_file;
  }
