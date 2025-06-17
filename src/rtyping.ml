open Core

open Rex
open Tlex
open Trex
open Typing

let debug_rtyping = ref false
let debug msg = if !debug_rtyping then Errors.debug_print ~f_name:(Some "rtyping.ml") msg

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
  let open Errors.OrErrors in
  let* traliases =
    try ok (Map.add_exn rs.trefi.traliases ~key:name ~data:(typ, doc_string))
    with _ -> error (Errors.type_error (Printf.sprintf "type alias %s already exists" name) pos) in
  let* tsubtypes = ok (Map.add_exn rs.s.tprog.tsubtypes ~key:name ~data:(Option.value_exn typ)) in
  let trefi =
    { rs.trefi with trtmts = TRType (pos, name, typ, doc_string) :: rs.trefi.trtmts;
                    traliases } in
  let  s = rs.s in
  let* s = if Map.mem s.tprog.taliases name then 
      ok { s with tprog = { s.tprog with taliases = Map.remove s.tprog.taliases name; tsubtypes } }
    else
      error (Errors.type_error
               (Printf.sprintf "type %s does not exist in %s and thus cannot be refined"
                  name (List.hd_exn rs.trefi.lex_file)) pos) in
      (* TODO[JD] get the full or relative path to the lex file being refined, currently it is only a string without even a file extension *)
  let* s = add_talias name typ doc_string s pos in
  ok { s; trefi }

let add_trrefined rs name : rt Errors.OrErrors.t =
  let open Errors.OrErrors in
  let f trefi =
    { trefi with trrefined = Set.add trefi.trrefined name } in
  ok (map rs f)

let add_trhidden name b label doc_string (rs: rt) (pos: LexingInfo.t) : rt Errors.OrErrors.t =
  let open Errors.OrErrors in
  let* trassumed = ok ((pos, name, b, label) :: rs.trefi.trassumed) in
  let* rs = add_trrefined rs name in
  let f trefi =
    { trefi with trtmts = TRAssume (pos, name, b, doc_string) :: trefi.trtmts;
                 trassumed } in
  if Map.mem rs.s.tprog.tevents name then
    ok (map rs f)
  else
    error (Errors.type_error (Printf.sprintf "event %s does not exist in %s and thus cannot be hidden" name (List.hd_exn rs.trefi.lex_file)) pos)
(* TODO[JD] get the full or relative path to the lex file being refined, currently it is only a string without even a file extension *)

let add_tautology (rs: rt) (pos: LexingInfo.t) (pos': LexingInfo.t) ?(assume: Tformula.t option=None) (f: Tformula.t) =
  { rs with trefi = { rs.trefi with tr_tautology = (pos, pos', assume, f) :: rs.trefi.tr_tautology } }

let update_mon (rs: rt) (f: mon_map -> Tformula.t list -> LexingInfo.t -> mon_map) (tfs: Tformula.t list) (pos: LexingInfo.t) =
  { rs with trefi = { rs.trefi with tr_mon = f rs.trefi.tr_mon tfs pos } }

let update_anti_mon (rs: rt) (f: mon_map -> Tformula.t list -> LexingInfo.t -> mon_map) (tfs: Tformula.t list) (pos: LexingInfo.t) =
  { rs with trefi = { rs.trefi with tr_anti_mon = f rs.trefi.tr_anti_mon tfs pos } }

let tpf_to_tformula (tpf: Tlex.Pattern.t) : Tformula.t =
  let module I = Eformula.Info in
  let f = Tformula.make_dummy (Tformula.conjs N tpf.fs) in
  match tpf.patt with
  | Pattern.PPresent -> f
  | PEventually i -> Tformula.make (Tformula.eventually i f) f.info
  | PAlways i -> Tformula.make (Tformula.always i f) f.info
  | PUntil (i, g) -> Tformula.make_dummy (Tformula.until N i g f)
  | POnce i -> Tformula.make (Tformula.once i f) f.info
  | PHistorically i -> Tformula.make (Tformula.historically i f) f.info
  | PSince (i, g) -> Tformula.make_dummy (Tformula.since N i f g)

let make_always_imp ~(close: bool) (lhs: Tformula.t) (rhs: Tformula.t) : Tformula.t =
  (** - [fv(f) = [x1; ... ; xn]]
      - [fv(g)\fv(f) = [y1; ... ; ym]]
      based on the truth value of [close], the following formulas in pseudo code are generated:
      {[if close then
        (forall x1.( ... forall xn . f)) -> (exists y1.( ... exists ym. g))
      else
        f -> (exists y1.( ... exists ym. g))]]}
  *)
  let fvs_f = Tformula.fv lhs in
  let fvs_g = Set.diff (Tformula.fv rhs) fvs_f in
  let f_imp_g =
    Tformula.make_dummy (
      Tformula.imp N lhs
        (List.fold_right (Base.Set.elements fvs_g)
            ~f:(fun x f -> Tformula.make_dummy (Tformula.exists x f))
            ~init:rhs)) in
  let f_imp_g =
    if close then
      let f_imp_g = List.fold_right (Base.Set.elements fvs_f)
                      ~f:(fun x f -> Tformula.make_dummy (Tformula.forall x f))
                      ~init:f_imp_g in
      Tformula.make_dummy (Tformula.forall "tp.0" f_imp_g)
    else f_imp_g in
  f_imp_g

let add_preds_to_mon_map (m: mon_map) (gs: Tformula.t list) (pos: LexingInfo.t) : mon_map =
  List.fold gs ~init:m
        ~f:(fun m x -> match x.form with
          | Predicate (p, _) ->
            let msg = Printf.sprintf "adding predicate %s to (anti)-monotonicity-map at %s (because of %s)" p (LexingInfo.to_string x.info.pos) (LexingInfo.to_string pos) in
            debug msg;
            Map.update m p ~f:(function
              | Some pos' -> LexingInfo.union_all [pos'; x.info.pos; pos]
              | None -> LexingInfo.union_all [x.info.pos; pos])
          | _ -> assert false)

let eq_form t t' = String.equal (Tformula.to_string t) (Tformula.to_string t')

let collect_potential_constitutive_replacements (pred: Tformula.t) (trules: trule list) : Tlex.Pattern.t list =
  List.filter_map ~f:(function
      | TConstitutive (_, tpf, gs') when List.mem gs' pred ~equal:eq_form -> Some tpf
      | _ -> None) trules

let collect_potential_exceptions (rs: rt) (old_idx: int) (new_trules: (trule *int) list) : (Tlex.Pattern.t * Tlex.Ref.t list * Tformula.t) list =
  let old_referenced_rules = Map.find_exn rs.trefi.tprog.rule_tree.exceptions old_idx in
  let filter_exceptions : (trule * int) -> (Tlex.Pattern.t * Tlex.Ref.t list * Tformula.t) option =
    function
      | TException (_, tpf, new_refs, p), new_idx
      | TExceptionC (_, tpf, new_refs, p, _), new_idx ->
        let new_referenced_rules = Map.find_exn rs.trefi.tprog.rule_tree.exceptions new_idx in
        if Util.int_list_equality_as_set old_referenced_rules new_referenced_rules then
          Some (tpf, new_refs, p)
        else
          let intersection = Util.intersection_of_int_lists old_referenced_rules new_referenced_rules in
          if List.is_empty intersection then
            None
          else
            begin
              let label_of_rule_idx idx = Map.find_exn rs.trefi.tprog.rule_tree.label_of_rule idx |> fst |> Label.string_of_label in
              let rule_labels_of_new_exception = List.map new_referenced_rules ~f:label_of_rule_idx in
              let rule_labels_of_old_exception = List.map old_referenced_rules ~f:label_of_rule_idx in
              let msg = Printf.sprintf
                "Checking exception replacement: partially matching exception replacement, but referenced rules are not equal. Old (%s):\n%s, New (%s):\n%s"
                (label_of_rule_idx old_idx)
                (String.concat ~sep:"\n" rule_labels_of_old_exception)
                (label_of_rule_idx new_idx)
                (String.concat ~sep:"\n" rule_labels_of_new_exception) in
              Errors.warn msg None;
              None
            end
      | _ -> None in
  List.filter_map ~f:filter_exceptions new_trules

let collect_potential_scopes (rs: rt) (old_idx: int) (new_trules: (trule * int) list) : (Tlex.Pattern.t * Tlex.Ref.t list * Tformula.t) list =
  let old_referenced_rules = Map.find_exn rs.trefi.tprog.rule_tree.scopes old_idx in
  let filter_scopes : (trule * int) -> (Tlex.Pattern.t * Tlex.Ref.t list * Tformula.t) option =
    function
      | TScope (_, tpf, new_refs, p), new_idx ->
        let new_referenced_rules = Map.find_exn rs.trefi.tprog.rule_tree.scopes new_idx in
        if Util.int_list_equality_as_set old_referenced_rules new_referenced_rules then
          Some (tpf, new_refs, p)
        else
          let intersection = Util.intersection_of_int_lists old_referenced_rules new_referenced_rules in
          if List.is_empty intersection then
            None
          else
            begin
              let label_of_rule_idx idx = Map.find_exn rs.trefi.tprog.rule_tree.label_of_rule idx |> fst |> Label.string_of_label in
              let rule_labels_of_new_scope = List.map new_referenced_rules ~f:label_of_rule_idx in
              let rule_labels_of_old_scope = List.map old_referenced_rules ~f:label_of_rule_idx in
              let msg = Printf.sprintf
                "Checking scope replacement: partially matching scope replacement, but referenced rules are not equal. Old (%s):\n%s, New (%s):\n%s"
                (label_of_rule_idx old_idx)
                (String.concat ~sep:"\n" rule_labels_of_old_scope)
                (label_of_rule_idx new_idx)
                (String.concat ~sep:"\n" rule_labels_of_new_scope) in
              Errors.warn msg None;
              None
            end
      | _ -> None in
  List.filter_map ~f:filter_scopes new_trules

let collect_new_obligations trules =
  List.filter_map ~f:(function
      | TObligation (_, tpf, tpg, _, _) -> Some (tpf, tpg)
      | _ -> None) trules

let make_obligations_conj obligations : Tformula.t =
  let tps_to_imp (tpf, tpg) = make_always_imp ~close:true (tpf_to_tformula tpf) (tpf_to_tformula tpg) in
  Tformula.make_dummy (Tformula.conjs N (List.map ~f:tps_to_imp obligations))
    
let make_implication_error pos pos' =
  let open Errors.OrErrors in
  error (Errors.refinement_error
          (Printf.sprintf
              "Cannot weaken constitutive rule defined at %s: cannot prove implication"
              (LexingInfo.to_string pos'))
          pos)

let check_regulative_replacement_implication old_obligation new_obligations pos pos' (rs:rt) : rt =
  let always_imp = make_always_imp ~close:true new_obligations old_obligation in
  let imp = Tformula.make_dummy (Tformula.imp N new_obligations always_imp) in
  add_tautology rs pos pos' ~assume:(Some new_obligations) imp

let check_regulative_replacement rs new_trules pos : trule -> rt = function
  | TObligation (pos', lhs, rhs, _, _) ->
    let new_obligations = collect_new_obligations new_trules in
    let new_obligations_conj = make_obligations_conj new_obligations in
    let old_obligation_imp = make_always_imp ~close:true (tpf_to_tformula lhs) (tpf_to_tformula rhs) in
    check_regulative_replacement_implication old_obligation_imp new_obligations_conj pos pos' rs
  | _ -> assert false

let check_constitutive_replacement_implication ~(weaken:bool) potential_replacements new_obligations_conj tf pos pos' (rs: rt) : rt =
  let f rs tpf' = 
    let tf' = tpf_to_tformula tpf' in
    let always_imp = if weaken then make_always_imp ~close:true tf' tf
                     else make_always_imp ~close:true tf tf' in
    let imp = Tformula.make_dummy (Tformula.imp N new_obligations_conj always_imp) in
    add_tautology rs pos pos' ~assume:(Some new_obligations_conj) imp in
  List.fold ~init:rs potential_replacements ~f

let check_constitutive_replacement ~(weaken: bool) (new_trules: trule list) (rs: rt) (pos: LexingInfo.t) : trule -> rt Errors.OrErrors.t = function
  | TExceptionC (pos', lhs, _, _, preds)
  | TConstitutive (pos', lhs, preds) ->
    let open Errors.OrErrors in
    let check_single pos' tpf rs g : rt =
      let potential_replacements = collect_potential_constitutive_replacements g new_trules in
      let new_obligations = collect_new_obligations new_trules in
      let new_obligations_conj = make_obligations_conj new_obligations in
      let tf = tpf_to_tformula tpf in
      check_constitutive_replacement_implication ~weaken potential_replacements new_obligations_conj tf pos pos' rs in
    let rs = List.fold ~init:rs ~f:(check_single pos' lhs) preds in
    if weaken then
      ok (update_anti_mon rs add_preds_to_mon_map preds pos)
    else
      ok (update_mon rs add_preds_to_mon_map preds pos)
  | _ -> assert false

let check_exception_replacement_implication ~(weaken:bool) potential_replacements new_obligations_conj (tf: Tformula.t) (pos: LexingInfo.t) (pos': LexingInfo.t) (rs: rt) : rt =
  let tpfs, _, _  = List.unzip3 potential_replacements in
  let f rs tpf' = 
    let tf' = tpf_to_tformula tpf' in
    let always_imp = if weaken then make_always_imp ~close:true tf' tf
                     else make_always_imp ~close:true tf tf' in
    let imp = Tformula.make_dummy (Tformula.imp N new_obligations_conj always_imp) in
    add_tautology rs pos pos' ~assume:(Some new_obligations_conj) imp in
  List.fold ~init:rs tpfs ~f

let check_scope_replacement_implication ~(weaken:bool) potential_replacements new_obligations_conj (tf: Tformula.t) (pos: LexingInfo.t) (pos': LexingInfo.t) (rs: rt) : rt =
  let tpfs, _, _  = List.unzip3 potential_replacements in
  let f rs tpf' = 
    let tf' = tpf_to_tformula tpf' in
    let always_imp = if weaken then make_always_imp ~close:true tf tf'
                     else make_always_imp ~close:true tf' tf in
    let imp = Tformula.make_dummy (Tformula.imp N new_obligations_conj always_imp) in
    add_tautology rs pos pos' ~assume:(Some new_obligations_conj) imp in
  List.fold ~init:rs tpfs ~f

let check_exception_replacement ~(weaken:bool) (new_trules: (trule * int) list) (rs: rt) pos (old_idx: int) : trule -> rt Errors.OrErrors.t = function
  | TExceptionC (pos', lhs, _, pred, _)
  | TException (pos', lhs, _, pred) ->
    let open Errors.OrErrors in
    let check_single pos' tpf g : rt =
      let _ = g in
      let potential_replacements = collect_potential_exceptions rs old_idx new_trules in
      let new_obligations = collect_new_obligations (List.map ~f:fst new_trules) in
      let new_obligations_conj = make_obligations_conj new_obligations in
      let tf = tpf_to_tformula tpf in
      check_exception_replacement_implication ~weaken potential_replacements new_obligations_conj tf pos pos' rs in
    let rs = check_single pos' lhs pred in
    if weaken then
      ok (update_anti_mon rs add_preds_to_mon_map [pred] pos)
    else
      ok (update_mon rs add_preds_to_mon_map [pred] pos)
  | _ -> assert false

let check_scope_replacement ~(weaken:bool) (new_trules: (trule * int) list) (rs: rt) pos (old_idx: int) : trule -> rt Errors.OrErrors.t = function
  | TScope (pos', lhs, _, pred) ->
    let open Errors.OrErrors in
    let check_single pos' tpf g : rt =
      let _ = g in
      let potential_replacements = collect_potential_scopes rs old_idx new_trules in
      let new_obligations = collect_new_obligations (List.map ~f:fst new_trules) in
      let new_obligations_conj = make_obligations_conj new_obligations in
      let tf = tpf_to_tformula tpf in
      check_scope_replacement_implication ~weaken potential_replacements new_obligations_conj tf pos pos' rs in
    let rs = check_single pos' lhs pred in
    if weaken then
      ok (update_anti_mon rs add_preds_to_mon_map [pred] pos)
    else
      ok (update_mon rs add_preds_to_mon_map [pred] pos)
  | _ -> assert false

(* Replacement checks *)

let check_trreplacement (kind: replace_kind)
                        (old_trule : trule * int)
                        (new_trules: (trule * int) list)
                        (rs: rt)
                        (pos: LexingInfo.t)
                        : rt Errors.OrErrors.t =
  let open Errors.OrErrors in
  match kind, old_trule with
  | Strengthen, ((TObligation _ as obl), _) -> (* Imp-R *)
     ok (check_regulative_replacement rs (List.map ~f:fst new_trules) pos obl)
  (* does not introduce any monotonicity constraints *)
  | Strengthen, ((TConstitutive _ as old_con), _) -> (* Imp-C+ *)
     check_constitutive_replacement ~weaken:false (List.map ~f:fst new_trules) rs pos old_con
  | Weaken, ((TConstitutive _ as old_con), _) -> (* Imp-C- *)
     check_constitutive_replacement ~weaken:true (List.map ~f:fst new_trules) rs pos old_con
  | Strengthen, ((TException _ as old_ex), old_idx) -> (* Imp-E+ *)
     check_exception_replacement ~weaken:false new_trules rs pos old_idx old_ex
  | Weaken, ((TException _ as old_ex), old_idx) -> (* Imp-E- *)
     check_exception_replacement ~weaken:true new_trules rs pos old_idx old_ex
  | Strengthen, ((TScope _ as old_sc), old_idx) -> (* Imp-E-*)
     check_scope_replacement ~weaken:false new_trules rs pos old_idx old_sc
  | Weaken, ((TScope _ as old_sc), old_idx) -> (* Imp-E+ *)
     check_scope_replacement ~weaken:true new_trules rs pos old_idx old_sc
  | Strengthen, ((TExceptionC _ as old_exc), old_idx) -> (* combination of Imp-E+ & Imp-C+ *)
     let* rs = check_exception_replacement ~weaken:false new_trules rs pos old_idx old_exc in
     check_constitutive_replacement ~weaken:false (List.map ~f:fst new_trules) rs pos old_exc
  | Weaken, ((TExceptionC _ as old_exc), old_idx) -> (* combination of Imp-E- & Imp-C- *)
     let* rs = check_exception_replacement ~weaken:true new_trules rs pos old_idx old_exc in
     check_constitutive_replacement ~weaken:true (List.map ~f:fst new_trules) rs pos old_exc 
  | Weaken, (TPermission _, _) ->
     (* TODO[JD]: Imp-R? merge with strengthen obligation as much as possible *)
     (* [JD] thoughts on permission rules as a concept:
        permissions have never been properly introduced and may
        not be fully compatible with obligations - these might be 
        2 different models:
        1. whenever something is not explicitly forbidden, it is permitted
        2. whenever something is not explicitly permitted, it is forbidden
        
        the necessity of permission for something can be expressed
        with an obligation, but it is unclear what it would mean that
        a rule expresses that A permits B, when everything (including B)
        was already permitted as long as no obligation forbids it *)
     assert false
  | Strengthen, (TPermission _, _) ->
     (* impossible *)
     (* same caveat as with strengthening permissions *)
     assert false
  | Weaken, (TObligation _, _) ->
     (* impossible cases *)
    assert false

let check_trreplacement_types (pos: LexingInfo.t) (old_trules: trule list) : unit Errors.OrErrors.t =
  let open Errors.OrErrors in
  let is_obligation = function
    | TObligation _ -> true
    | _ -> false in
  let contains_obligation trules =
    List.exists trules ~f:is_obligation in
  let only_obligations = List.for_all ~f:is_obligation in
  if contains_obligation old_trules && not (only_obligations old_trules) then
    (* TODO[JD]: is this error message understandable or does it need more clarification? *)
    let msg = "Cannot replace obligations and other rule types in the same replace-rule" in
    error (Errors.refinement_error msg pos)
  else
    ok ()

let check_new_trule_types (tprog: tprog) (pos: LexingInfo.t) (new_trules: (trule * int) list) : unit Errors.OrErrors.t =
  (** Checks that the new rules in a replacements contain at most one non-obligaiton rule *)
  let open Errors.OrErrors in
  let non_obligations =
    let f = function
      | TObligation _, _ -> None
      | _, idx -> Some (Label.RuleTree.string_of_rule_idx tprog.rule_tree idx) in
    List.filter_map ~f new_trules in
  if List.length non_obligations <= 1 then
    ok ()
  else
    let msg = Printf.sprintf
      "The rules used to replace one or more other rules can either be a set of obligations or a (possibly empty) set of obligations combined with exactly one non-obligation rule, but here multiple non-obligation rules are provided:\n%s"
      (String.concat ~sep:"\n" non_obligations) in
    error (Errors.refinement_error msg pos)

let add_trreplacements (kind: replace_kind) (old_refs: Tlex.Ref.t list) (new_refs: Tlex.Ref.t list) doc_string (rs: rt) pos : rt Errors.OrErrors.t =
  let open Errors.OrErrors in
  let trules_and_ids_from_refs (refs: Tlex.Ref.t list) : (trule * int) list Errors.OrErrors.t = 
    let  rtref_exprs = List.map ~f:Ref.to_rtref_expr refs in
    let* rule_ids =
      let f (ref: Label.RuleTree.rtref_expr) =
        Label.RuleTree.find_rules_in_tree ref.pos ref.label rs.s.tprog.rule_tree.tree in
      all (List.map rtref_exprs ~f) >| List.concat in
    let f = function
      | TSRule (_, idx, _, _, trule, _) when List.mem rule_ids idx ~equal:Int.equal -> Some (trule, idx)
      | _ -> None in
    ok (List.filter_map ~f rs.s.tprog.tstmts) in
  let* old_trules = trules_and_ids_from_refs old_refs in
  let* new_trules = trules_and_ids_from_refs new_refs in
  let* _ = check_new_trule_types rs.s.tprog pos new_trules in
  let* _ = check_trreplacement_types pos (List.map ~f:fst old_trules) in
  let* rs =
    let f rs old_rule = check_trreplacement kind old_rule new_trules rs pos in
    fold_best_effort ~init:rs ~f old_trules in
  let f trefi =
    { trefi with trtmts = TRReplace (pos, kind, old_refs, new_refs, doc_string) :: trefi.trtmts;
                 trreplacements = (pos, kind, old_refs, new_refs) :: rs.trefi.trreplacements } in
  ok (map rs f)

(* Visitors *)

let type_rrule (rs: rt) pos : rtmt -> rt Errors.OrErrors.t =
  let open Errors.OrErrors in
  function
  | RRule (_, rule_id, type_fixes, rrule, doc_string) -> begin
      let label' = Label.set_rule_id_force rule_id rs.s.label  in
      let _ = Label.valid_rule_label pos label' in
      let c = TypeTerm.of_alist_ctxt ~subtypes:rs.s.tprog.tsubtypes type_fixes in
      let rule_num = fresh () in
      let* t_vars, names, trule, rrule =
        let process_rule s ctxt = function
          | Refine (pos, pf1, f2) ->
             let names = List.map ~f:(fun f ->
                             match f.form with Formula.Predicate (event_name, _) -> event_name
                                             | _ -> assert false) f2 in
             combine2 ctxt pf1 f2 (collect_pformula' s.tprog) (collect_formulas s.tprog)
               (fun ctxt tpf1 tf2 ->
                 ok (ctxt, names, TConstitutive (pos, tpf1, tf2), TRefine (pos, tpf1, tf2)))
        in process_rule rs.s c rrule
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

let collect_rtmt (rs: rt) : rtmt -> rt Errors.WithErrors.t =
  let open Errors.OrErrors in
  let we = witherror ~default:rs in
  function
  | RStmt stmt ->
     Errors.WithErrors.(
      let* s = collect_stmt rs.s stmt in
      let  tstmts = List.tl_exn s.tprog.tstmts @ [List.hd_exn s.tprog.tstmts] in
      let  s = { s with tprog = { s.tprog with tstmts } } in
      ok { s; trefi = { rs.trefi with
                        trtmts = TRStmt (List.hd_exn s.tprog.tstmts) :: rs.trefi.trtmts } }
     )
  | RRule (pos,  _, _, _, _) as rrule ->
     we (type_rrule rs pos rrule)
  | RType (pos, name, typ, doc_string) ->
     we (add_tralias name typ doc_string rs pos)
  | RReplace (pos, kind, old_refs, new_refs, doc_string) ->
     let rs = 
       let* old_reference_labels = all (List.map ~f:(merge_reference_with_label pos rs.s.label) old_refs) in 
       let* new_reference_labels = all (List.map ~f:(merge_reference_with_label pos rs.s.label) new_refs) in
       add_trreplacements kind old_reference_labels new_reference_labels doc_string rs pos in
     we rs
  | RAssume (pos, name, b, doc_string) ->
     let label = Label.set_rule_id_force (Some ("assume_" ^ name)) rs.s.label in
     we (add_trhidden name b label doc_string rs pos)

(* Checking of tautologies *)

let check_tautology tprog (pos, pos', (assume: Tformula.t option), (f: Tformula.t)) =
  let open Errors.OrErrors in
  let ctxt = TypeTerm.empty_ctxt in
  let* ctxt, assume = match assume with
    | None -> ok (ctxt, None)
    | Some assume ->
       let* ctxt, assume = collect_formula tprog ctxt (Tformula.to_formula assume) in
       let assume = type_formula ctxt assume in
       ok (ctxt, Some assume) in
  let* ctxt, f = collect_formula tprog ctxt (Tformula.to_formula f) in
  let f = type_formula ctxt f in
  if (Smt.is_tautology tprog ~assume f)
  then ok ()
  else make_implication_error pos pos'

(* Main typing function *)

let do_type (s: Typing.t) (refi: refi) : (Typing.t * trefi) Errors.WithErrors.t =
  let open Errors.WithErrors in
  let label = Label.set_rule_id_force None s.label in
  let s = { s with tprog = { s.tprog with tstmts = s.tprog.tstmts @ [Tlex.TSSection (Article 0, label, "refinement", None)] } } in
  let init = { s; trefi = { trempty with lex_file = refi.lex_file; base_file_type = refi.base_file_type } } in
  (* First pass: type statements *)
  let* rs: rt = fold refi.rtmts ~init ~f:collect_rtmt in
  (* TODO[FH]: Implement typing of additional exceptions or generate errors *)
  (* Second pass: compute rule contexts *)
  let* rule_ctxts = rule_ctxts rs.s.tprog in
  debug (String.concat ~sep:", " (List.map (Map.to_alist rs.s.tprog.tsubtypes) ~f:(fun (a, b) -> a ^ " < " ^ (TypeTerm.ttt_to_string b))));
  let tprog = { rs.s.tprog with rule_ctxts } in
  (* Third pass: re-type statements *)
  let tprog = do_retype tprog in
  (* Fourth pass: check tautologies *)
  let* _  = all (List.map ~f:(Errors.OrErrors.witherror ~default:())
                   (List.map ~f:(check_tautology tprog) rs.trefi.tr_tautology)) in
  ok (rs.s, { rs.trefi with tprog; trtmts = List.rev rs.trefi.trtmts })

