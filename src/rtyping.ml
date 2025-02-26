open Core

open Rex
open Tlex
open Trex
open Typing

(* Typing state *)

type rt =
  {
    s:     t;
    trefi: trefi;
  }

let rempty =
  {
    s     = Typing.empty;
    trefi = trempty;
  }

let map rs f = { rs with trefi = f rs.trefi }

let add_trtmt tstmt trtmt rs =
  let open Errors.OrErrors in
  let s = { rs.s with tprog = { rs.s.tprog with tstmts = rs.s.tprog.tstmts @ [tstmt] } } in
  ok { s; trefi = { rs.trefi with trtmts = trtmt :: rs.trefi.trtmts } }

let add_tralias name typ doc_string rs pos =
  (* TODO[FH]: check that the type exists in the underlying lex code / that we can overwrite it *)
  let open Errors.OrErrors in
  let* traliases =
    try ok (Map.add_exn rs.trefi.traliases ~key:name ~data:(typ, doc_string))
    with _ -> error (Errors.type_error (Printf.sprintf "type alias %s already exists" name) pos) in
  let trefi =
    { rs.trefi with trtmts = TRType (pos, name, typ, doc_string) :: rs.trefi.trtmts;
                    traliases } in
  let  s = rs.s in
  let  s = { s with tprog = { s.tprog with taliases = Map.remove s.tprog.taliases name } } in
  let* s = add_talias name typ doc_string s pos in
  ok { s; trefi }

let add_trrefined rs name =
  let open Errors.OrErrors in
  let f trefi =
    { trefi with trrefined = Set.add trefi.trrefined name } in
  ok (map rs f)

let add_trhidden name b label doc_string rs pos =
  (* TODO[FH]: check that the event exists in the underlying lex code *)
  let open Errors.OrErrors in
  let* trassumed = ok ((pos, name, b, label) :: rs.trefi.trassumed) in
  let* rs = add_trrefined rs name in
  let f trefi =
    { trefi with trtmts = TRAssume (pos, name, b, doc_string) :: trefi.trtmts;
                 trassumed } in
  ok (map rs f)

let add_trreplacements kind refs1 refs2 doc_string rs pos =
  (* TODO[FH]: check implications + monotonicity with Z3 *)
  let open Errors.OrErrors in
  let* trreplacements = ok ((pos, kind, refs1, refs2) :: rs.trefi.trreplacements) in
  let f trefi =
    { trefi with trtmts = TRReplace (pos, kind, refs1, refs2, doc_string) :: trefi.trtmts;
                 trreplacements } in
  ok (map rs f)

(* Visitors *)

let type_rrule rs pos =
  let open Errors.OrErrors in
  function
  | RRule (_, rule_id, type_fixes, rrule, doc_string) -> begin
      let label' = Label.set_rule_id_force rule_id rs.s.label  in
      let _ = Label.valid_rule_label pos label' in
      let t_vars = Map.of_alist_exn (module String) type_fixes in
      let rule_num = fresh () in
      let* t_vars, names, trule, rrule = 
        let process_rule s t_vars = function
          | Refine (pos, pf1, f2) ->
             let names = List.map ~f:(fun f ->
                             match f.form with Formula.Predicate (event_name, _) -> event_name
                                             | _ -> assert false) f2 in
             combine2 t_vars pf1 f2 (type_pformula' s.tprog) (type_formulas s.tprog)
               (fun t_vars tpf1 tf2 ->
                 ok (t_vars, names, TConstitutive (pos, tpf1, tf2), TRefine (pos, tpf1, tf2)))
        in process_rule rs.s t_vars rrule
      in
      let var_to_add = (rule_num, t_vars) in
      let rule_to_add = (pos, rule_num, label') in
      let doc_string' = Option.map doc_string ~f:(fun x -> TALex x) in
      let tstmt = TSRule (pos, rule_num, label', type_fixes, trule, doc_string') in
      let trtmt = TRRule (pos, rule_num, label', type_fixes, rrule, doc_string') in
      let* rs = fold_best_effort names ~init:rs ~f:add_trrefined in
      ok { rs with
          trefi = { rs.trefi with trtmts         = trtmt       :: rs.trefi.trtmts;
                                  trvars_to_add  = var_to_add  :: rs.trefi.trvars_to_add;
                                  trrules_to_add = rule_to_add :: rs.trefi.trrules_to_add;
                                  trstmts_to_add = tstmt       :: rs.trefi.trstmts_to_add  } }
    end
  | _ -> assert false

let type_rtmt rs : rtmt -> rt Errors.WithErrors.t =
  let open Errors.OrErrors in
  let we = witherror ~default:rs in
  function
  | RStmt stmt ->
     Errors.WithErrors.(
      let* s = type_stmt rs.s stmt in
      let  tstmts = List.tl_exn s.tprog.tstmts @ [List.hd_exn s.tprog.tstmts] in
      let  s = { s with tprog = { s.tprog with tstmts } } in
      ok { s; trefi = { rs.trefi with
                        trtmts = TRStmt (List.hd_exn s.tprog.tstmts) :: rs.trefi.trtmts } }
     )
  | RRule (pos,  _, _, _, _) as rrule -> 
     we (type_rrule rs pos rrule)
  | RType (pos, name, typ, doc_string) -> 
     we (add_tralias name typ doc_string rs pos)
  | RReplace (pos, kind, refs1, refs2, doc_string) ->
     let rs = 
       let* reference_labels1 = all (List.map ~f:(merge_reference_with_label pos rs.s.label) refs1) in 
       let* reference_labels2 = all (List.map ~f:(merge_reference_with_label pos rs.s.label) refs2) in
       add_trreplacements kind reference_labels1 reference_labels2 doc_string rs pos in
     we rs
  | RAssume (pos, name, b, doc_string) ->
     let label = Label.set_rule_id_force (Some ("assume_" ^ name)) rs.s.label in
     we (add_trhidden name b label doc_string rs pos)

(* Main typing function *)

let do_type (s: Typing.t) (refi: refi) : (Typing.t * trefi) Errors.WithErrors.t =
  let open Errors.WithErrors in
  (*Map.iter_keys ~f:print_endline s.tprog.tevents;*)
  let label = Label.set_rule_id_force None s.label in
  let s = { s with tprog = { s.tprog with tstmts = s.tprog.tstmts @ [Tlex.TSSection (Article 0, label, "refinement", None)] } } in
  let init = { s; trefi = { trempty with lex_file = refi.lex_file } } in
  (* First pass: type statements *)
  let* rs = fold refi.rtmts ~init ~f:type_rtmt in
  (* TODO[FH]: Implement typing of additional exceptions or generate errors *)
  let* variables = check_var_types rs.s.tprog in
  ok (rs.s, { rs.trefi with tprog = { rs.s.tprog with variables };
                            trtmts = List.rev rs.trefi.trtmts })

