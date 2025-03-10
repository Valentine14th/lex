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

let add_tralias name (typ: TypeTerm.t option) doc_string (rs: rt) (pos: LexingInfo.t) : rt Errors.OrErrors.t =
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

let add_trrefined rs name : rt Errors.OrErrors.t =
  let open Errors.OrErrors in
  let f trefi =
    { trefi with trrefined = Set.add trefi.trrefined name } in
  ok (map rs f)

let add_trhidden name b label doc_string (rs: rt) (pos: LexingInfo.t) : rt Errors.OrErrors.t =
  (* TODO[FH]: check that the event exists in the underlying lex code *)
  let open Errors.OrErrors in
  let* trassumed = ok ((pos, name, b, label) :: rs.trefi.trassumed) in
  let* rs = add_trrefined rs name in
  let f trefi =
    { trefi with trtmts = TRAssume (pos, name, b, doc_string) :: trefi.trtmts;
                 trassumed } in
  ok (map rs f)

let merge_t_vars m (tf: Tformula.t) : (string, TypeTerm.t, String.comparator_witness) Map.t =
  Map.merge ~f:(fun ~key:_ -> function
      | `Left a -> Some a
      | `Right a -> Some a
      | `Both (a, _) -> Some a)
    m (Map.of_alist_exn (module String) tf.info.t_vars)

let tpf_to_tformula (tpf: Tlex.Pattern.t) : Tformula.t =
  let module I = Eformula.Info in
  let t_vars' = List.fold tpf.fs ~init:(Map.empty (module String)) ~f:merge_t_vars in
  let t_vars = Map.to_alist t_vars' in
  let f = Tformula.make (Tformula.conjs N tpf.fs) { Tformula.Info.dummy with t_vars } in
  match tpf.patt with
  | Pattern.PPresent -> f
  | PEventually i -> Tformula.make (Tformula.eventually i f) f.info
  | PAlways i -> Tformula.make (Tformula.always i f) f.info
  | PUntil (i, g) -> Tformula.make (Tformula.until N i g f)
                       { Tformula.Info.dummy with t_vars = Map.to_alist (merge_t_vars t_vars' g) }
  | POnce i -> Tformula.make (Tformula.once i f) f.info
  | PHistorically i -> Tformula.make (Tformula.historically i f) f.info
  | PSince (i, g) -> Tformula.make (Tformula.since N i f g)
                       { Tformula.Info.dummy with t_vars = Map.to_alist (merge_t_vars t_vars' g) }

let check_trreplacement (kind: replace_kind) (old_trule: trule) (new_trules: trule list) (rs: rt) pos : unit Errors.OrErrors.t =
  let open Errors.OrErrors in
  let eq t t' = String.equal (Tformula.to_string t) (Tformula.to_string t') in
  let make_always_imp close f g =
    let fvs_f = Tformula.fv f in
    let fvs_g = Set.diff (Tformula.fv g) fvs_f in
    let t_vars' = List.fold [f; g] ~init:(Map.empty (module String)) ~f:merge_t_vars in
    let t_vars = Map.to_alist t_vars' in
    let f_imp_g = Tformula.make (
                      Tformula.imp N f
                        (List.fold_right (Base.Set.elements fvs_g)
                           ~f:(fun x f -> Tformula.make (Tformula.exists x f)
                                            { Tformula.Info.dummy with t_vars = f.info.t_vars } )
                           ~init:g))
                    { Tformula.Info.dummy with t_vars } in
    let f_imp_g = if close then
                    let f_imp_g = List.fold_right (Base.Set.elements fvs_f)
                                    ~f:(fun x f -> Tformula.make (Tformula.forall x f)
                                                     { Tformula.Info.dummy with t_vars = f.info.t_vars })
                                    ~init:f_imp_g in
                    Tformula.make (Tformula.forall "tp.0" f_imp_g)
                      { Tformula.Info.dummy with t_vars = t_vars @ [("tp.0", TypeTerm.TypeConst Dom.TInt)] }
                  else
                    f_imp_g in
    f_imp_g in
  match kind, old_trule with
  | Strengthen, TConstitutive (pos', tpf, gs) ->
     (* TODO[FH]: Check monotonicity *)
     let check_strengthen_constitutive pos' tpf g =
       let potential_replacements =
         List.filter_map ~f:(function
             | TConstitutive (_, tpf, gs') when List.mem gs' g ~equal:eq -> Some tpf
             | _ -> None) new_trules in
       let new_obligations =
         List.filter_map ~f:(function
             | TObligation (_, tpf, tpg, _, _) -> Some (tpf, tpg)
             | _ -> None) new_trules in
       let new_obligations_conj =
         let t_vars' =
           List.fold new_obligations ~init:(Map.empty (module String))
             ~f:(fun m (tpf, tpg) ->
               merge_t_vars (merge_t_vars m (tpf_to_tformula tpf)) (tpf_to_tformula tpg)) in
         let t_vars = Map.to_alist t_vars' in
         Tformula.make (
             Tformula.conjs N (
                 List.map ~f:(fun (tpf, tpg) ->
                     make_always_imp true (tpf_to_tformula tpf) (tpf_to_tformula tpg))
                   new_obligations))
           { Tformula.Info.dummy with t_vars } in
       let tf = tpf_to_tformula tpf in
       debug ("check_strengthen_constitutive " ^ Tformula.to_string tf);
       debug ("new_trules: " ^ Int.to_string (List.length new_trules));
       debug ("potential_replacements: " ^ Int.to_string (List.length potential_replacements));
       let b = List.exists potential_replacements ~f:(
                   fun tpf' -> let tf' = tpf_to_tformula tpf' in
                               let t_vars' = List.fold [tf; tf'] ~init:(Map.empty (module String)) ~f:merge_t_vars in
                               let t_vars = Map.to_alist t_vars' in
                               let imp = Tformula.make
                                           (Tformula.imp N
                                              new_obligations_conj (make_always_imp false tf' tf))
                                           { Tformula.Info.dummy with t_vars } in
                               Smt.is_tautology rs.s.tprog ~assume:(Some new_obligations_conj) imp) in
       if b then
         ok ()
       else
         error (Errors.refinement_error
                  (Printf.sprintf
                     "Cannot strengthen constitutive rule defined at %s: cannot prove implication"
                     (LexingInfo.to_string pos'))
                  pos) in
     let* _ = all (List.map ~f:(check_strengthen_constitutive pos' tpf) gs) in
     ok ()
  | _ -> (* TODO[FH]: Other cases *) assert false

let add_trreplacements (kind: replace_kind) (refs1: Tlex.Ref.t list) (refs2: Tlex.Ref.t list) doc_string (rs: rt) pos : rt Errors.OrErrors.t =
  (* TODO[FH]: check implications + monotonicity with Z3 *)
  let open Errors.OrErrors in
  let* trreplacements  = ok ((pos, kind, refs1, refs2) :: rs.trefi.trreplacements) in
  let rules_by_refs refs = 
    let  rtref_exprs = List.map ~f:Ref.to_rtref_expr refs in
    let* rules_idx =
      all (List.map rtref_exprs ~f:(fun ref ->
               Label.RuleTree.find_rules_in_tree ref.pos ref.label rs.s.tprog.rule_tree.tree))
      >| List.concat in
    let f = function
      | TSRule (_, idx, _, _, trule, _) when List.mem rules_idx idx ~equal:Int.equal -> Some trule
      | _ -> None in
    ok (List.filter_map ~f rs.s.tprog.tstmts) in
  let* old_trules = rules_by_refs refs1 in
  let* new_trules = rules_by_refs refs2 in
  let* _ = fold_best_effort ~init:() ~f:(
               fun () old -> check_trreplacement kind old new_trules rs pos) old_trules in
  let f trefi =
    { trefi with trtmts = TRReplace (pos, kind, refs1, refs2, doc_string) :: trefi.trtmts;
                 trreplacements } in
  ok (map rs f)

(* Visitors *)

let type_rrule (rs: rt) pos : rtmt -> rt Errors.OrErrors.t =
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

let type_rtmt (rs: rt) : rtmt -> rt Errors.WithErrors.t =
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

