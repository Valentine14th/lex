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
  let refs = List.concat_map trefi.trreplacements ~f:(fun (_, _, refs1, _) -> refs1) in
  let rtref_exprs = List.map ~f:Ref.to_rtref_expr refs in
  let* rules_in_tree =
    all (List.map rtref_exprs ~f:(fun ref ->
             Label.RuleTree.find_rules_in_tree ref.pos ref.label eprog.rule_tree.tree)) in
  let ecrules = List.fold_left (List.concat rules_in_tree) ~init:eprog.ecrules ~f:Map.remove in
  ok { eprog with ecrules }

let hide_and_replace_eprog trefi (eprog: eprog) : eprog Errors.OrErrors.t =
  (* update types *)
  let eprog = update_types trefi eprog in
  (* hide events *)
  let eprog = hide_events trefi eprog in
  (* make mapped events internal *)
  let eprog = internalize_events trefi eprog in
  (* replace rules *)
  replace_rules trefi eprog

(* Main typing function *)

let do_type (trefi: Trex.trefi) (b: Interval.v) : Erex.erefi Errors.OrErrors.t =
  let open Errors.OrErrors in
  (* TODO[FH]: check that the refinement is valid *)
  (* TODO[FH]: check that all events have been mapped *)
  let* eprog = Enforceability.do_type trefi.tprog b in
  let* eprog = hide_and_replace_eprog trefi eprog in
  let erules = Enforceability.erules_from_tcrules (Enforceability.create_tcrules trefi.tprog) in
  ok {
    eprog;
    ertmts = List.map trefi.trtmts ~f:(type_estmt erules);
    theory = trefi.theory;
  }
