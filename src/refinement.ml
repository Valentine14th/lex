open Core
open Tlex
open Elex
open Trex
open Erex

module Interval = MFOTL_lib.Interval
module Enftype = MFOTL_lib.Enftype

(* Visitors *)

let type_trrule = function
  | TRefine (pos', pf, g) -> ERefine (pos', Elex.epf_of_tpf pf, Eformula.of_tformulas g)

let type_estmt erule_map = function
  | TRStmt tstmt ->
     ERStmt (Enforceability.type_tstmt erule_map tstmt)
  | TRRule (pos, i, label, type_fixes, trrule, doc_string) ->
     ERRule (pos, i, label, type_fixes, type_trrule trrule, doc_string)
  | TRType (pos, name, typ, doc_string) ->
     ERType (pos, name, typ, doc_string)
  | TRReplace (pos, kind, refs1, refs2, doc_string) ->
     ERReplace (pos, kind, refs1, refs2, doc_string)
  | TRHide (pos, name, doc_string) ->
     ERHide (pos, name, doc_string)

let insert_refinement_rules erule_map (trefi: trefi) (eprog: eprog) : (tprog * eprog) Errors.OrErrors.t =
  let open Errors.OrErrors in
  let variables  = List.fold_left trefi.trvars_to_add
                     ~init:eprog.variables
                     ~f:(fun m (key, data) -> Map.add_exn m ~key ~data) in
  let* rule_tree = fold_best_effort trefi.trrules_to_add
                     ~init:eprog.rule_tree
                     ~f:(fun s (pos, ri, label) -> Label.RuleTree.add_rule pos ri label s) in
  let estmts     = List.fold_left trefi.trstmts_to_add
                     ~init:eprog.estmts
                     ~f:(fun estmts tstmt ->
                       estmts @ [Enforceability.type_tstmt erule_map tstmt]) in
  let tstmts     = trefi.tprog.tstmts @ trefi.trstmts_to_add in
  (* add ecrules, compilation_order *)
  ok ({ trefi.tprog with variables; rule_tree; tstmts },
      { eprog with estmts; variables; rule_tree })
  

let update_types (trefi: trefi) (eprog: eprog) : eprog =
  let f ~key ~data ealiases = Map.update ealiases key ~f:(fun _ -> data) in
  let ealiases = Map.fold trefi.traliases ~init:eprog.ealiases ~f in
  { eprog with ealiases }

let hide_events (trefi: trefi) (eprog: eprog) : eprog =
  let make_ecrule rule_id (pos, name) =
    let (_, vars, _, _) = Map.find_exn eprog.eevents name in
    let f (x, typ) = Eformula.ETerm.make (Eformula.ETerm.var x) { pos = LexingInfo.dummy; typ } in
    let pred = Eformula.make_dummy (Eformula.Predicate (name, List.map ~f vars)) in
    let edisjunct = {
        rule_id;
        rule_type       = TRTConstitutive;
        rule_pos        = pos;
        def_pos         = pos;
        pf              = Elex.Pattern.make PPresent [Eformula.make_dummy Eformula.FF];
        exceptions      = [];
        scopes          = [];
        fv_renaming     = Map.empty (module String);
        params_original = [];
        params_new      = [];
      } in
    let edisjuncts = Map.of_alist_exn (module Int) [0, edisjunct] in
    let enf_ecdefinition_dis = Some (ESdd [ESlhsSPformula (ESpfFormula 0)]) in
    ECDefinitionDis (edisjuncts, pred, Enftype.abs, enf_ecdefinition_dis) in
  let idx = Option.value (Option.map ~f:fst (Map.max_elt eprog.ecrules)) ~default:(-1) + 1 in
  let f (idx, eprog) (pos, name) =
    let ecrule = make_ecrule idx (pos, name) in
    (idx + 1, { eprog with ecrules = Map.add_exn eprog.ecrules ~key:idx ~data:ecrule }) in
  snd (List.fold_left ~init:(idx, eprog) ~f trefi.trhidden)

let internalize_events (trefi: trefi) (eprog: eprog) : eprog =
  let internalize_event name eprog =
    let update_event (event_type, params, _, doc_string) =
      (event_type, params, Enftype.itl, doc_string) in
    let eevents = 
      Map.update eprog.eevents name
        ~f:(function None -> assert false | Some ev -> update_event ev) in
    { eprog with eevents }
  in List.fold_right ~init:eprog ~f:internalize_event (Set.elements trefi.trrefined)

let replace_rules (trefi: trefi) (eprog: eprog) : eprog Errors.OrErrors.t =
  let open Errors.OrErrors in
  let refs = List.concat_map trefi.trreplacements ~f:(fun (_, _, refs1, _) -> (*print_endline ("REFINEMENT3 " ^ String.concat ~sep:"," (List.map ~f:Tlex.Ref.to_string refs1));*) refs1) in
  let rtref_exprs = List.map ~f:Ref.to_rtref_expr refs in
  let* rules_in_tree =
    all (List.map rtref_exprs ~f:(fun ref ->
             (*print_endline ("Ref " ^ Lex.Ref.to_string ref.ref);*)
             let* r = Label.RuleTree.find_rules_in_tree ref.pos ref.label eprog.rule_tree.tree in
             (*print_endline (Int.to_string (List.length r));*)
             ok r
      )) in
  (*print_endline (Int.to_string (List.length rules_in_tree));*)
  let ecrules = List.fold_left (List.concat rules_in_tree) ~init:eprog.ecrules ~f:(fun m i -> (*print_endline ("hello "  ^ Int.to_string i);*) Map.remove m i) in
  ok { eprog with ecrules }

let hide_and_replace_eprog trefi (eprog: eprog) : (tprog * eprog) Errors.OrErrors.t =
  let open Errors.OrErrors in
  (* add refinement rules *)
  let erules = Enforceability.erules_from_tcrules (Enforceability.create_tcrules trefi.tprog) in
  let* tprog, eprog = insert_refinement_rules erules trefi eprog in
  let* eprog =
    eprog
    |> update_types trefi
    |> hide_events trefi
    |> internalize_events trefi
    |> replace_rules trefi in
  (* make mapped events internal *)
  (* replace rules *)
  (*print_endline (Elex.string_of_eprog eprog);
  print_endline ("REPLACEMENT2 "^ String.concat ~sep:";" (List.map ~f:(fun (_, _, refs, _) -> (String.concat ~sep:"," (List.map refs ~f:Tlex.Ref.to_string ))) trefi.trreplacements));*)
  ok (tprog, eprog)

(* Main typing function *)

let do_type (trefi: Trex.trefi) (b: Interval.v) : Erex.erefi Errors.OrErrors.t =
  let open Errors.OrErrors in
  (* TODO[FH]: check that the refinement is valid *)
  (* TODO[FH]: check that all events have been mapped *)
  let* eprog = Enforceability.do_type trefi.tprog b in
  let* tprog, eprog = hide_and_replace_eprog trefi eprog in
  let erules = Enforceability.erules_from_tcrules (Enforceability.create_tcrules tprog) in
  ok {
    eprog;
    ertmts = List.map trefi.trtmts ~f:(type_estmt erules);
    lex_file = trefi.lex_file;
  }
