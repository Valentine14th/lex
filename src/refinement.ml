open Core
open Tlex
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

let hide_events (trefi: trefi) (tprog: tprog) : tprog =
  let make_tsrule (pos, name, label) =
    let (_, vars, _, _) = Map.find_exn tprog.tevents name in
    let f (x, typ) = Eformula.ETerm.make (Eformula.ETerm.var x) { pos = LexingInfo.dummy; typ } in
    let pred = Tformula.make_dummy (Tformula.Predicate (name, List.map ~f vars)) in
    let idx = Typing.fresh () in
    let trule = TConstitutive (
                    LexingInfo.dummy,
                    Tlex.Pattern.make PPresent [Tformula.make_dummy Tformula.FF],
                    [pred]
                  ) in
    TSRule (pos, idx, label, [], trule, None) in
  let f tprog (pos, name, label) =
    let tsrule = make_tsrule (pos, name, label) in
    { tprog with tstmts = tprog.tstmts @ [tsrule] } in
  List.fold_left ~init:tprog ~f trefi.trhidden

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
  (*print_endline (Int.to_string (List.length rules_in_tree));*)
  let f = function
    | TSRule (_, idx, _, _, _, _) -> not (List.mem rules_idx_to_replace idx ~equal:Int.equal)
    | _ -> true in
  let tstmts = List.filter ~f tprog.tstmts in
  ok { tprog with tstmts }

let hide_and_replace trefi (tprog: tprog) : tprog Errors.OrErrors.t =
  let open Errors.OrErrors in
  ok tprog
  >>= insert_refinement_rules trefi
  >| update_types trefi
  >| hide_events trefi
  >| internalize_events trefi
  >>= replace_rules trefi
  (*print_endline (Elex.string_of_eprog eprog);
  print_endline ("REPLACEMENT2 "^ String.concat ~sep:";" (List.map ~f:(fun (_, _, refs, _) -> (String.concat ~sep:"," (List.map refs ~f:Tlex.Ref.to_string ))) trefi.trreplacements));*)


(* Main typing function *)

let do_type (trefi: Trex.trefi) (b: Interval.v) : Erex.erefi Errors.OrErrors.t =
  let open Errors.OrErrors in
  (* TODO[FH]: check that the refinement is valid *)
  (* TODO[FH]: check that all events have been mapped *)
  (*let* eprog = Enforceability.do_type trefi.tprog b in*)
  let* tprog = hide_and_replace trefi trefi.tprog in
  print_endline (Tlex.string_of_tprog tprog);
  let* eprog = Enforceability.do_type tprog b in
  let erules = Enforceability.erules_from_tcrules (Enforceability.create_tcrules tprog) in
  ok {
    eprog;
    ertmts = List.map trefi.trtmts ~f:(type_estmt erules);
    lex_file = trefi.lex_file;
  }
