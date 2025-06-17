open Core

open TypeTerm
open Term
open Lex
open Tlex

let debug_typing = ref false
let debug msg = if !debug_typing then Errors.debug_print ~f_name:(Some "typing.ml") msg


(* Typing state *)

type t =
  {
    tprog: tprog;
    label: Label.t;
    exceptions_first_pass: (int * Tformula.t * Tlex.Ref.t list) list;
    scopes_first_pass: (int * Tformula.t * Tlex.Ref.t list) list;
    articles: (ident, ident list, String.comparator_witness) Map.t; (* map from law[0] identifiers to all article[0] identifiers in a particular law, used to enforce unique article identifiers *)
  }

let empty =
  {
    tprog = tempty;
    label = Label.empty;
    exceptions_first_pass = [];
    scopes_first_pass = [];
    articles = Map.empty (module String);
  }

let add_tstmt tstmt s =
  let open Errors.OrErrors in
  ok { s with tprog = Tlex.add_tstmt tstmt s.tprog }

let add_talias alias typ doc_string s pos =
  let open Errors.OrErrors in
  let* tprog = Tlex.add_talias alias typ doc_string s.tprog pos in
  ok { s with tprog }

let add_tfunction name arg_types return_type doc_string s pos =
  let open Errors.OrErrors in
  let* tprog = Tlex.add_tfunction name arg_types return_type doc_string s.tprog pos in
  ok { s with tprog }

let add_tevent event_type name args pol ds s (pos: LexingInfo.t) =
  let open Errors.OrErrors in
  let* tprog = Tlex.add_tevent event_type name args pol ds s.tprog pos in
  ok { s with tprog }

let add_vars i vs s =
  let open Errors.OrErrors in
  ok { s with tprog = Tlex.add_vars i vs s.tprog }

let add_rule pos rule_num label s =
  let open Errors.OrErrors in
  let* tprog = Tlex.add_rule pos rule_num label s.tprog in
  ok { s with tprog }

let add_section pos label s =
  let open Errors.OrErrors in
  let* tprog = Tlex.add_section pos label s.tprog in
  ok { s with tprog }

let add_exception_first_pass i f (refs: Tlex.Ref.t list) s =
  let open Errors.OrErrors in
  ok { s with exceptions_first_pass = (i,f,refs)::s.exceptions_first_pass }

let add_scope_first_pass i f refs s =
  let open Errors.OrErrors in
  ok { s with scopes_first_pass = (i,f,refs)::s.scopes_first_pass}

let set_labels pos section_kind label s =
  let open Errors.OrErrors in
  let* articles = match section_kind with
    | Article 0 ->
       let* law_name =
         begin try ok (Label.qualified_name_of_law ~exn:true s.label.law)
               with _ -> error (Errors.label_error ("Article \"" ^ fst label ^ "\" must be inside a law, but is not") pos)
         end in
      let articles = Map.find_multi s.articles law_name in
      if List.exists articles ~f:(String.equal (fst label)) then
        error (Errors.label_error ("Article \"" ^ fst label ^ "\" already exists in Law \"" ^ law_name ^ "\"") pos)
      else
        ok (Map.add_multi s.articles ~key:law_name ~data:(fst label))
    | _ -> ok s.articles
  in
  let* label = Label.set pos section_kind label s.label in
  ok { s with label; tprog = Tlex.set_labels pos label s.tprog; articles }

(* Visitors: collecting constraints *)

let c = ref (-1) 
let fresh () = incr c; !c

let constrain_base_type_ctxt' c pos ttt tts =
  match ttt with
  | TConst tt when List.mem tts tt ~equal:Dom.equal_tt -> c
  | TConst _ ->
     raise (CtxtError (
                Printf.sprintf "type clash: found %s, expected base type in [%s]"
                  (ttt_to_string ttt) (String.concat ~sep:", " (List.map ~f:Dom.tt_to_string tts))))
  | _ -> constrain_base_type_ctxt c pos (List.map ~f:(fun tt -> [ttt, tt]) tts)

let collect_unot c pos ttt =
  constrain_base_type_ctxt' c pos ttt [Dom.TBool; Dom.TInt], ttt

let collect_usub c pos ttt =
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TFloat; Dom.TSpan; Dom.TMoney "*"], ttt

let collect_badd c pos (ttt, ttt') =
  let c, ttt = unify_ctxt ttt ttt' c in
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TFloat; Dom.TSpan; Dom.TStr; Dom.TMoney "*"], ttt

let collect_bsub c pos (ttt, ttt') =
  let c, ttt = unify_ctxt ttt ttt' c in
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TFloat; Dom.TSpan], ttt

let collect_bmul c pos (ttt, ttt') =
  let c, ttt = unify_ctxt ttt ttt' c in
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TFloat], ttt

let collect_band c pos (ttt, ttt') =
  let c, ttt = unify_ctxt ttt ttt' c in
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TBool], ttt

let collect_beq c _ (ttt, ttt') =
  let c, _ = unify_ctxt ttt ttt' c in
  c, TConst Dom.TBool

let collect_blt c pos (ttt, ttt') =
  let c, ttt = unify_ctxt ttt ttt' c in
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TFloat; Dom.TTime; Dom.TSpan; Dom.TMoney "*"],
  TConst Dom.TBool

let rec collect_term (s: tprog) (c: ctxt) (v: Term.t):
          (ctxt * TTerm.t) Errors.OrErrors.t =
  let open Errors.OrErrors in
  let* c, ttrm = 
    match v.trm with
    | Var x ->
       let* ctxt, typ =
         if TypeTerm.mem c.ctxt x then
           ok (c.ctxt, TypeTerm.get_ttt_exn x c.ctxt)
         else
           let ctxt, ttt = TypeTerm.fresh_ttt c.ctxt in
           ok (TypeTerm.type_var x ttt ctxt)
       in
       (*print_endline ("collect_term " ^ String.concat ~sep:", " (TypeTerm.vars c.ctxt));*)
       ok ({ c with ctxt }, TTerm.make (TTerm.var x) { pos = v.info.pos; typ })
    | Const d ->
       let ctxt, typ = TypeTerm.fresh_ttt c.ctxt in
       let c = constrain_base_type_ctxt { c with ctxt } v.info.pos [[typ, Dom.tt_of_domain d]] in
       ok (c, TTerm.make (TTerm.const d) { pos = v.info.pos; typ  })
    | App (f_name, trms) ->
       begin
         let f (c, trms) trm (_, arg_type) =
           let* c, trm = collect_term s c trm in
           let c, typ = unify_ctxt trm.info.typ arg_type c in
           ok (c, { trm with info = { trm.info with typ } } :: trms)
         in
         let aux c arg_types typ =
           let* folded = fold2 trms arg_types ~init:(c, []) ~f in
           begin match folded with
           | Base.List.Or_unequal_lengths.Ok (c, trms) ->
              ok (c, TTerm.make (TTerm.app f_name (List.rev trms)) { pos = v.info.pos; typ })
           | Base.List.Or_unequal_lengths.Unequal_lengths ->
              let err_msg = Printf.sprintf "Function %s expects %d arguments, found %d"
                              f_name (List.length arg_types) (List.length trms) in
              error (Errors.type_error err_msg v.info.pos)
           end in
         match Map.find s.tfunctions f_name with
         | Some (arg_types, typ, _) ->
            let arg_names, arg_types = List.unzip arg_types in
            let ctxt, typ_arg_types = convert_with_fresh_ttts c.ctxt (typ :: arg_types) in
            let typ, arg_types = List.hd_exn typ_arg_types, List.tl_exn typ_arg_types in
            aux { c with ctxt } (List.zip_exn arg_names arg_types) typ
         | None ->
            let err_msg = Printf.sprintf "Function %s is undefined" f_name in
            error (Errors.type_error err_msg v.info.pos)
       end
    | Unop (op, trm) ->
       begin
         let f_op = match op with
           | UNot -> collect_unot
           | USub -> collect_usub in
         let* c, trm = collect_term s c trm in
         let* c, typ =
           try ok (f_op c trm.info.pos trm.info.typ)
           with CtxtError err_msg -> error (Errors.type_error err_msg v.info.pos) in
         ok (c, TTerm.make (TTerm.unop op trm) { pos = v.info.pos; typ })
       end
    | Binop (trm, op, trm') ->
       begin
         let f_op = match op with
           | BAdd -> collect_badd
           | BSub -> collect_bsub
           | BMul | BDiv | BPow -> collect_bmul
           | BAnd | BOr | BXor -> collect_band
           | BEq | BNeq -> collect_beq
           | BLt | BLeq | BGt | BGeq -> collect_blt
         in
         let* c, trm  = collect_term s c trm  in
         let* c, trm' = collect_term s c trm' in
         let* c, typ =
           try ok (f_op c trm.info.pos (trm.info.typ, trm'.info.typ))
           with CtxtError err_msg -> error (Errors.type_error err_msg v.info.pos) in
         ok (c, TTerm.make (TTerm.binop trm op trm') { pos = v.info.pos; typ })
       end
    | Proj (trm, p) ->
       let ctxt, typ = TypeTerm.fresh_ttt c.ctxt in
       let* c, trm = collect_term s { c with ctxt } trm in
       let c = constrain_fields_type_ctxt c trm.info.pos (trm.info.typ, false, [p, typ]) in
       ok (c, TTerm.make (TTerm.proj trm p) { pos = v.info.pos; typ })
    | Record kvs ->
       let ctxt, typ = TypeTerm.fresh_ttt c.ctxt in
       let* c, kvs = fold_best_effort kvs ~init:({ c with ctxt }, []) ~f:(fun (c, kvs) (k, v) ->
                         let* c, trm = collect_term s c v in
                         ok (c, (k, trm) :: kvs)) in
       let kvs = List.rev kvs in
       let fields = List.map kvs ~f:(fun (k, v) -> (k, v.info.typ)) in
       let c = constrain_fields_type_ctxt c v.info.pos (typ, true, fields) in
       ok (c, TTerm.make (TTerm.record kvs) { pos = v.info.pos; typ }) in
  debug (Printf.sprintf "collect_term.c(%s) = %s" (Term.value_to_string v) (to_string_ctxt c));
  ok (c, ttrm)

let collect_terms event_name trms c pos s : (ctxt * TTerm.t list) Errors.OrErrors.t =
  let open Errors.OrErrors in
  let* args = match Map.find s.tevents event_name with
    | Some (_, args, _, _) -> ok args
    | None -> let err_msg = Printf.sprintf "Event '%s' is undefined" event_name
              in error (Errors.type_error err_msg pos)
  in
  let f c ((_, arg_type), trm) =
    let* c, trm = collect_term s c trm in
    debug (Printf.sprintf "collect_terms.c(arg_type=%s, trm=%s)..."
             (ttt_to_string arg_type) (TTerm.value_to_string trm));
    let* c, typ =
      try ok (unify_ctxt trm.info.typ arg_type c)
      with CtxtError err_msg -> error (Errors.type_error err_msg pos) in
    debug (Printf.sprintf "collect_terms.c(arg_type=%s, trm=%s) = %s"
             (ttt_to_string arg_type) (TTerm.value_to_string trm) (to_string_ctxt c));
    ok (c, { trm with info = { trm.info with typ } })
  in
  match List.zip args trms with
  | Base.List.Or_unequal_lengths.Ok args_trms ->
     let c, trms' = fold_map_best_effort ~init:c ~f args_trms in
     let trms' = (all trms') in
     trms' >| (fun trms' -> (c, trms'))
  | Base.List.Or_unequal_lengths.Unequal_lengths ->
     let err_msg = Printf.sprintf
                     "Number of arguments doesn't match for event '%s'"
                     event_name  in
     error (Errors.type_error err_msg pos)

let unpack_functional tevents (trm': Term.t) (trm: Term.t) : (ident * Term.t list * event_type) option =
  match trm.trm with
  | Term.App (f, trms) ->
     (match Map.find tevents f with
      | Some (Event (_, Functional) as et, _, _, _) ->
         Some (f, trms @ [trm'], et)
      | _ -> None)
  | _ -> None

let unpack_variable tevents (trm': Term.t) (trm: Term.t) : (ident * 'e list * event_type) option =
  match trm.trm with
  | Term.Var x ->
     (match Map.find tevents x with
      | Some (Event (_, Variable) as et, _, _, _) ->
         Some (x, [trm'], et)
      | _ -> None)
  | _ -> None

let unpack_special_eq tevents trm trm' : (ident * Term.t list * event_type) option =
  List.find_map
    [unpack_functional tevents trm trm';
     unpack_functional tevents trm' trm;
     unpack_variable tevents trm trm';
     unpack_variable tevents trm' trm]
    ~f:(fun x -> x)

let collect_asum c pos ttt =
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TFloat; Dom.TSpan; Dom.TMoney "*"],
  ttt

let collect_amed c pos ttt =
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TFloat; Dom.TSpan; Dom.TTime; Dom.TMoney "*"],
  ttt

let collect_acnt c pos ttt =
  constrain_base_type_ctxt' c pos ttt [Dom.TInt; Dom.TFloat; Dom.TSpan; Dom.TTime; Dom.TStr; Dom.TMoney "*"],
  ttt

let rec collect_formula (s: tprog) ?(event_type=Event (false, Standard)) (c: ctxt) (f: Formula.t): (ctxt * Tformula.t) Errors.OrErrors.t =
  let open Errors.OrErrors in
  debug (Printf.sprintf "collect_formula(%s)..." (Formula.to_string f));
  let* c, form, event_type_opt = match f.form with
  | Formula.TT -> ok (c, Tformula.tt, None)
  | FF -> ok (c, Tformula.ff, None)
  | EqConst (({ trm = Binop (x, BEq, y); _ } as trm), ((Dom.Bool true) as d)) -> begin
    match unpack_special_eq s.tevents x y with
    | Some (event_name, trms, event_type) ->
       let* c, f = collect_formula s ~event_type c (Formula.make (Formula.predicate event_name trms) f.info) in
       ok (c, f.form, Some event_type)
    | None ->
       let* c, trm = collect_term s c trm in
       let c = constrain_base_type_ctxt' c trm.info.pos trm.info.typ [Dom.tt_of_domain d] in
       ok (c, Tformula.EqConst (trm, d), None)
    end
  | EqConst (trm, d) ->
     let* c, trm = collect_term s c trm in
     let c = constrain_base_type_ctxt' c trm.info.pos trm.info.typ [Dom.tt_of_domain d] in
     ok (c, Tformula.EqConst (trm, d), None)
  | Predicate (event_name, trms) ->
     let* c, trms = collect_terms event_name trms c f.info.pos s in
     ok (c, Tformula.predicate event_name trms, Some event_type)
  | Agg (u, op, x, y, f) ->
     let f_op = match op with
       | ASum | AAvg | AStd -> collect_asum
       | AMed | AMin | AMax -> collect_amed
       | ACnt | AAssign -> collect_acnt
     in
     let* c, tf = collect_formula s c f in
     let* c, tx = collect_term s c x in
     let* c, ttt =
       try ok (f_op c tx.info.pos tx.info.typ)
       with CtxtError err_msg -> error (Errors.type_error err_msg tx.info.pos) in
     let c = { c with ctxt = fst (TypeTerm.type_var u ttt c.ctxt) } in
     ok (c, Tformula.agg u op tx y tf, None)
  | Neg f ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.neg f, None)
  | And (side, fs) ->
     let c, fs = fold_map_best_effort fs ~init:c ~f:(collect_formula s) in
     let* fs = all fs in
     ok (c, Tformula.conjs side fs, None)
  | Or (side, fs) ->
     let c, fs = fold_map_best_effort fs ~init:c ~f:(collect_formula s) in
     let* fs = all fs in
     ok (c, Tformula.disjs side fs, None)
  | Imp (side, f, g) ->
     combine2 c f g (collect_formula s) (collect_formula s)
       (fun c f g -> ok (c, Tformula.imp side f g, None))
  | Exists (x, f) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.exists x f, None)
  | Forall (x, f) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.forall x f, None)
  | Prev (i, f) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.prev i f, None)
  | Next (i, f) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.next i f, None)
  | Once (i, f) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.once i f, None)
  | Eventually (i, f) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.eventually i f, None)
  | Historically (i, f) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.historically i f, None)
  | Always (i, f) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.always i f, None)
  | Since (side, i, f, g) ->
     combine2 c f g (collect_formula s) (collect_formula s)
       (fun c f g -> ok (c, Tformula.since side i f g, None))
  | Until (side, i, f, g) ->
     combine2 c f g (collect_formula s) (collect_formula s)
       (fun c f g -> ok (c, Tformula.until side i f g, None))
  | Type (f, ty) ->
     let* c, f = collect_formula s c f in
     ok (c, Tformula.ftype f ty, None)
  | Predicate' _ | Let _ | Let' _  | Top _ ->
     raise (Invalid_argument (Printf.sprintf "typing not implemented for %s" (Formula.to_string f)))
  in
  debug (Printf.sprintf "collect_formula.c(%s) = %s"
           (Formula.to_string f) (to_string_ctxt c));
  ok (c, Tformula.{ form; info = Tformula.{ pos = f.info.pos; event_type_opt } })

let collect_patt s c (pf: Lex.Pattern.patt) : (ctxt * Pattern.patt) Errors.OrErrors.t =
  let open Errors.OrErrors in
  match pf with
  | PPresent -> ok (c, Pattern.PPresent)
  | PEventually i -> ok (c, Pattern.PEventually i)
  | PAlways i -> ok (c, Pattern.PAlways i)
  | PUntil (i, f) -> let* c, f = collect_formula s c f in ok (c, Pattern.PUntil (i, f))
  | POnce i -> ok (c, Pattern.POnce i)
  | PHistorically i -> ok (c, Pattern.PHistorically i)
  | PSince (i, f) -> let* c, f = collect_formula s c f in ok (c, Pattern.PSince (i, f))

let collect_formulas s c (fs: Formula.t list): (ctxt * Tformula.t list) Errors.OrErrors.t =
  let open Errors.OrErrors in
  let c, fs = fold_map_best_effort fs ~init:c ~f:(collect_formula s) in
  (all fs) >| (fun fs -> c, fs)

let collect_pformula tprog c (pf: Lex.Pattern.t):
      ('free_vars * ctxt * Pattern.t) Errors.OrErrors.t =
  let open Errors.OrErrors in
  combine2 c pf.fs pf.patt (collect_formulas tprog) (collect_patt tprog)
    (fun c fs patt ->
      let tpf = Pattern.make patt fs in
      let vars = Pattern.fv tpf in
      ok (vars, c, tpf))

let collect_pformula' tprog c pf : (ctxt * Pattern.t) Errors.OrErrors.t =
  let open Errors.OrErrors in
  (collect_pformula tprog c pf) >| (fun (_, c, pf) -> (c, pf))

let merge_reference_with_label pos (l: Label.t) (ref_expr: Lex.Ref.t) : Tlex.Ref.t Errors.OrErrors.t =
  let open Errors.OrErrors in
  begin match Label.highest_level l with
  | (Label.LSection (Article 0, _)) ->
     let init = Label.qualified_label l in
     let rule_id = ref_expr.rule in
     let aux acc (level, name) = Label.set pos level (name, None) acc in
     let* label = fold ~init:init ~f:aux ref_expr.sks in
     let label = Label.set_rule_id rule_id label in
     ok (Ref.from_lex_ref ref_expr label)
  | _ ->
     let rule_id = ref_expr.rule in
     let aux acc (level, name) = Label.set pos level (name, None) acc in
     let* label = fold ~init:l ~f:aux ref_expr.sks in
     let label = Label.set_rule_id rule_id label in
     ok (Ref.from_lex_ref ref_expr label)
  end

let collect_rule (s: t) : stmt -> t Errors.OrErrors.t =
  let open Errors.OrErrors in
  function
  | SRule (pos, rule_id, type_fixes, rule, doc_string) -> begin
      let label' = Label.set_rule_id_force rule_id s.label  in
      let _ = Label.valid_rule_label pos label' in
      let c = TypeTerm.of_alist_ctxt ~subtypes:s.tprog.tsubtypes type_fixes in
      let rule_num = fresh () in
      debug (Printf.sprintf "collect_rule(%d)" rule_num);
      let section_kinds_are_in_order (k1, s1) (k2, s2) = match compare_section_kind k1 k2 with
        | i when i = 0 -> 
          let err_msg = Printf.sprintf "Section kind %s is defined more than once: '%s' and '%s'" (string_of_section_kind k1) s1 s2 in
          error (Errors.reference_error err_msg pos)
        | i when i < 0 -> 
          let err_msg = Printf.sprintf "Section kinds inside reference must be strictly 'decreasing', but '%s \"%s\"' is followed by '%s \"%s\"' which is at a greater level" 
            (string_of_section_kind k1) s1 (string_of_section_kind k2) s2
          in
          error (Errors.reference_error err_msg pos)
        | _ -> ok (k2, s2)
      in
      let decreasing_section_kinds (r: Lex.Ref.t) = match r with
        | {sks=[]; rule=None; _} -> error (Errors.reference_error "references must contain at least one reference" r.pos)
        | {sks=r::rs; _} -> ok ((fold ~init:r ~f:section_kinds_are_in_order rs) |> ignore)
        | {sks=[]; rule=Some _; _} -> ok ()
      in
      let* (s, c), rule = 
        let var_term_of_ident_and_positions c x =
          TTerm.{ trm = TTerm.var x;
                  info = { pos = LexingInfo.dummy;
                           typ = TypeTerm.get_ttt_exn_ctxt x  c } } in
        let arg_of_ident_and_positions c x =
          (x, TypeTerm.get_ttt_exn_ctxt x c) in
        let rec process_rule s c = function
          | Exception (pos, pf, refs) ->
             let _ = List.map ~f:decreasing_section_kinds refs in
             (*debug (String.concat ~sep:"\n" (List.map refs ~f:Lex.Ref.to_string));*)
             let reference_labels = List.map ~f:(merge_reference_with_label pos s.label) refs in
             let* reference_labels = all reference_labels in
             (*debug (String.concat ~sep:"\n" (List.map reference_labels ~f:(fun r -> Label.string_of_label r.label)));*)
             let p_name = "Exception" ^ string_of_int rule_num in (* TODO: mark 'Exception' as an internal name and prevent user-defined events to start with that *)
             let* vars, c, tpf = collect_pformula s.tprog c pf in
             let terms = List.map (Set.elements vars) ~f:(var_term_of_ident_and_positions c) in
             let args = List.map (Set.elements vars) ~f:(arg_of_ident_and_positions c) in
             let pred = Tformula.make (Tformula.predicate p_name terms)
                          { Tformula.Info.dummy with event_type_opt = Some (Event (false, Standard)) } in
             let* s' = add_exception_first_pass rule_num pred reference_labels s in
             let* s' = add_tevent Lex.Exception p_name args Enftype.itl None s' LexingInfo.dummy in 
             ok ((s', c), TException (pos, tpf, reference_labels, pred))
          | Scope (pos, pf, refs) ->
             let _ = List.map ~f:decreasing_section_kinds refs in
             let reference_labels = List.map ~f:(fun tref -> merge_reference_with_label pos s.label tref) refs in
             let* reference_labels = all reference_labels in
             let p_name = "Scope" ^ string_of_int rule_num in (* TODO: mark 'Scope' as an internal name and prevent user-defined events to start with that *)
             let* vars, c, tpf = collect_pformula s.tprog c pf in
             let terms = List.map (Set.elements vars) ~f:(var_term_of_ident_and_positions c) in
             let args = List.map (Set.elements vars) ~f:(arg_of_ident_and_positions c) in
             let pred = Tformula.make (Tformula.predicate p_name terms)
                          { Tformula.Info.dummy with event_type_opt = Some (Event (false, Standard)) } in
             let* s' = add_scope_first_pass rule_num pred reference_labels s in
             let* s' = add_tevent Lex.Exception p_name args Enftype.itl None s' LexingInfo.dummy in 
             ok ((s', c), TScope (pos, tpf, reference_labels, pred))
          | Obligation (pos, pf1, pf2, rt, rcs) ->
             combine2 c pf1 pf2 (collect_pformula' s.tprog) (collect_pformula' s.tprog)
               (fun c tpf1 tpf2 -> ok ((s, c), TObligation (pos, tpf1, tpf2, rt, rcs)))
          | Permission (pos, pf1, pf2, rt, rcs) ->
             combine2 c pf1 pf2 (collect_pformula' s.tprog) (collect_pformula' s.tprog)
               (fun c tpf1 tpf2 -> ok ((s, c), TPermission (pos, tpf1, tpf2, rt, rcs)))
          | Constitutive (pos, pf1, f2) ->
             combine2 c pf1 f2 (collect_pformula' s.tprog) (collect_formulas s.tprog)
               (fun c tpf1 tf2 -> ok ((s, c), TConstitutive (pos, tpf1, tf2)))
          | ExceptionC (pos, pf1, refs, f2) ->
             combine2 (s, c) pf1 f2
               (fun (s, c) pf1 -> process_rule s c (Exception (pos, pf1, refs)))
               (fun (s, c) f2 -> process_rule s c (Constitutive (pos, pf1, f2)))
               (fun (s, c) tf tg ->
                 match tf, tg with
                 | TException (pos, tpf1, reference_labels, pref), TConstitutive (_, _, tf2)
                   -> ok ((s, c), TExceptionC (pos, tpf1, reference_labels, pref, tf2))
                 | _, _ -> assert false)
        in process_rule s c rule
      in
      let* s' = add_vars rule_num c s in
      let* s'' = add_rule pos rule_num label' s' in
      let doc_string' = Option.map doc_string ~f:(fun x -> TALex x) in
      debug (Printf.sprintf "ctxt(%d) = %s" rule_num (to_string_ctxt c));
      add_tstmt (TSRule (pos, rule_num, label', type_fixes, rule, doc_string')) s''
    end
  | _ -> assert false

let collect_stmt (s: t) : stmt -> t Errors.WithErrors.t =
  let open Errors.OrErrors in
  let we = witherror ~default:s in
  function
  | SImport (pos, import_format, idents) ->
     we (add_tstmt (TSImport (pos, idents, import_format)) s)
  | SSection (pos, section_kind, label_description, title) ->
     let s' = let* s = set_labels pos section_kind (label_description, title) s in
              add_section pos s.label s in
     let title' = Option.map title ~f:(fun x -> TALex x) in
     we (s' >>= (fun s' -> add_tstmt (TSSection (section_kind, s.label, label_description, title')) s'))
  | SRule _ as rule ->
     we (collect_rule s rule)
  | SEvent (pos, event_type, name, args, pol, ds) ->
     we (add_tevent event_type name args pol ds s pos)
  | SType (pos, name, typ, doc_string) ->
     we (add_talias name typ doc_string s pos)
  | SFunction (pos, name, arg_types, return_type, doc_string) ->
     we (add_tfunction name arg_types return_type doc_string s pos)
  | SNote (_, text) ->
     we (add_tstmt (TSNote text) s)

(* Visitors: typing *)

let rec type_term ctxt (v: TTerm.t) : TTerm.t =
  let trm = match v.trm with
  | TTerm.Var x -> TTerm.Var x
  | Const c -> Const c
  | App (f_name, trms) -> App (f_name, List.map ~f:(type_term ctxt) trms)
  | Unop (op, trm) -> Unop (op, type_term ctxt trm)
  | Binop (trm, op, trm') -> Binop (type_term ctxt trm, op, type_term ctxt trm')
  | Proj (trm, p) -> Proj (type_term ctxt trm, p)
  | Record kvs -> Record (List.map ~f:(fun (k, v) -> (k, type_term ctxt v)) kvs)
  in let term = TTerm.{ trm; info = { v.info with typ = TypeTerm.eval_ctxt v.info.typ ctxt } } in
     debug (Printf.sprintf "type_term(%s, %s) = %s" (TypeTerm.to_string_ctxt ctxt) (TTerm.value_to_string term) (ttt_to_string term.info.typ));
     term
       
let type_terms ctxt (vs: TTerm.t list) : TTerm.t list =
  List.map ~f:(type_term ctxt) vs

let rec type_formula ctxt (f : Tformula.t) : Tformula.t =
  let form = match f.form with
    | Tformula.TT -> Tformula.TT
    | FF -> FF
    | EqConst (t, d) -> EqConst (type_term ctxt t, d)
    | Predicate (event_name, trms) -> Predicate (event_name, type_terms ctxt trms)
    | Agg (u, op, x, y, f) -> Agg (u, op, type_term ctxt x, y, type_formula ctxt f)
    | Neg f -> Neg (type_formula ctxt f)
    | And (side, fs) -> And (side, List.map ~f:(type_formula ctxt) fs)
    | Or (side, fs) -> Or (side, List.map ~f:(type_formula ctxt) fs)
    | Imp (side, f, g) -> Imp (side, type_formula ctxt f, type_formula ctxt g)
    | Exists (x, f) -> Exists (x, type_formula ctxt f)
    | Forall (x, f) -> Forall (x, type_formula ctxt f)
    | Prev (i, f) -> Prev (i, type_formula ctxt f)
    | Next (i, f) -> Next (i, type_formula ctxt f)
    | Once (i, f) -> Once (i, type_formula ctxt f)
    | Eventually (i, f) -> Eventually (i, type_formula ctxt f)
    | Historically (i, f) -> Historically (i, type_formula ctxt f)
    | Always (i, f) -> Always (i, type_formula ctxt f)
    | Since (side, i, f, g) -> Since (side, i, type_formula ctxt f, type_formula ctxt g)
    | Until (side, i, f, g) -> Until (side, i, type_formula ctxt f, type_formula ctxt g)
    | Type (f, ty) -> Type (type_formula ctxt f, ty)
    | Predicate' _ | Let _ | Let' _  | Top _ ->
       raise (Invalid_argument
                (Printf.sprintf "typing not implemented for %s" (Tformula.to_string f)))
  in
  debug (Printf.sprintf "type_formula(%s, %s)" (Tformula.to_string f) (TypeTerm.to_string_ctxt ctxt));
  { f with form }

let type_patt ctxt (tpf: Tlex.Pattern.patt) : Tlex.Pattern.patt =
  match tpf with
  | PPresent -> Pattern.PPresent
  | PEventually i -> Pattern.PEventually i
  | PAlways i -> Pattern.PAlways i
  | PUntil (i, f) -> Pattern.PUntil (i, type_formula ctxt f)
  | POnce i -> Pattern.POnce i
  | PHistorically i -> Pattern.PHistorically i
  | PSince (i, f) -> Pattern.PSince (i, type_formula ctxt f)

let type_formulas ctxt (tfs: Tformula.t list): Tformula.t list =
  List.map ~f:(type_formula ctxt) tfs

let type_pformula ctxt (tpf: Pattern.t): Pattern.t =
  Pattern.make (type_patt ctxt tpf.patt) (type_formulas ctxt tpf.fs)

let type_rule (tprog: tprog) : tstmt -> tstmt =
  function
  | TSRule (pos, rule_id, label, type_fixes, rule, doc_string) -> begin
      let rc = Map.find_exn tprog.rule_ctxts rule_id in
      debug (Printf.sprintf "type_rule.rc(%d) = %s" rule_id (to_string_ctxt rc));
      let rule = match rule with
        | TException (pos, tpf, reference_labels, pred) ->
           TException (pos, type_pformula rc tpf, reference_labels, type_formula rc pred)
        | TScope (pos, tpf, reference_labels, pred) ->
           TScope (pos, type_pformula rc tpf, reference_labels, type_formula rc pred)
        | TObligation (pos, tpf1, tpf2, rt, rcs) ->
           TObligation (pos, type_pformula rc tpf1, type_pformula rc tpf2, rt, rcs)
        | TPermission (pos, tpf1, tpf2, rt, rcs) ->
           TPermission (pos, type_pformula rc tpf1, type_pformula rc tpf2, rt, rcs)
        | TConstitutive (pos, tpf1, tf2) ->
           TConstitutive (pos, type_pformula rc tpf1, type_formulas rc tf2)
        | TExceptionC (pos, tpf1, reference_labels, pref, tf2) ->
           TExceptionC (pos, type_pformula rc tpf1, reference_labels,
                        type_formula rc pref, type_formulas rc tf2) in
      TSRule (pos, rule_id, label, type_fixes, rule, doc_string)
    end
  | _ -> assert false

let type_stmt (tprog: tprog) : tstmt -> tstmt =
  function
  | TSRule _ as rule -> type_rule tprog rule
  | tstmt -> tstmt

(* Checking of variable types *)
    
let merge_ctxt tprog pos (m1: ctxt) (m2: ctxt) (label: ident) : ctxt Errors.OrErrors.t = 
  let open Errors.OrErrors in
  try
    let m2 = concrete_ctxt tprog.taliases m2 in
    ok (TypeTerm.merge_ctxt m1 m2)
  with CtxtError err_msg ->
    error (Errors.type_error (Printf.sprintf "Error in rule '%s': %s" label err_msg) pos)

let rule_ctxts tprog : (int, ctxt, Int.comparator_witness) Map.t Errors.WithErrors.t =
  let open Errors.WithErrors in
  let var_equivalence_classes =
    Label.RuleTree.rules_with_shared_variable_scopes tprog.rule_tree in
  debug (Printf.sprintf "var_equivalence_classes = [%s]"
           (String.concat ~sep:", "
              (List.map var_equivalence_classes
                 ~f:(fun rs -> Printf.sprintf "{%s}"
                                 (String.concat ~sep:", "
                                    (List.map ~f:Int.to_string (Set.elements rs)))))));
  let merge_rule_ctxt ctxt rule_key =
    let ctxt' = Map.find_exn tprog.rule_ctxts rule_key in
    debug (Printf.sprintf "merge %s (rule %d) into %s..."
             (to_string_ctxt ctxt') rule_key (to_string_ctxt ctxt));
    let pos = Label.RuleTree.pos_of_rule_idx tprog.rule_tree rule_key in
    let label = Label.RuleTree.string_of_rule_idx tprog.rule_tree rule_key in
    debug "reach here";
    let ctxt = merge_ctxt tprog pos ctxt ctxt' label in
    Errors.OrErrors.witherror ~default:(TypeTerm.of_subtypes_ctxt tprog.tsubtypes) ctxt in
  let merge_rule_ctxts rule_keys =
    fold (Set.elements rule_keys) ~init:(TypeTerm.of_subtypes_ctxt tprog.tsubtypes) ~f:merge_rule_ctxt in
  let var_equivalence_ctxts = List.map var_equivalence_classes ~f:merge_rule_ctxts in
  let* var_equivalence_ctxts = all var_equivalence_ctxts in
  let set_rule_ctxts v m rule_id =
    debug (Printf.sprintf "set_rule_ctxts(rule_id=%d, v=%s)" rule_id (to_string_ctxt v));
    Map.update m rule_id ~f:(fun _ -> v) in
  let set_class_ctxts m v rule_ids = Set.fold rule_ids ~init:m ~f:(set_rule_ctxts v) in
  let rule_ctxts = List.fold2_exn ~init:(Map.empty (module Int))
                    ~f:set_class_ctxts var_equivalence_ctxts var_equivalence_classes in
  ok rule_ctxts

(* Main typing function *)

let do_type_exceptions (s: t) : tprog Errors.WithErrors.t =
  let open Errors.WithErrors in
  let we = Errors.OrErrors.witherror in
  let* tprog = fold s.exceptions_first_pass ~init:s.tprog
                 ~f:(fun acc (i,f,refs) -> we ~default:acc (Tlex.add_exception i f refs acc)) in
  let* tprog = fold s.scopes_first_pass ~init:tprog
                 ~f:(fun acc (i,f,refs) -> we ~default:acc (Tlex.add_scope i f refs acc)) in
  let* rule_ctxts = rule_ctxts tprog in
  ok { tprog with tstmts = List.rev tprog.tstmts; rule_ctxts }

let do_retype (tprog: tprog) : tprog =
  let tstmts = List.map ~f:(type_stmt tprog) tprog.tstmts in
  { tprog with tstmts }

let do_type (tprog: tprog) (prog: prog) : (t * tprog) Errors.WithErrors.t =
  let open Errors.WithErrors in
  let init = { empty with tprog } in
  (* First pass: type statements, collect contraints *)
  let* s = fold prog.stmts ~init ~f:collect_stmt in
  (* Second pass: exceptions, constraint resolution *)
  let* tprog = do_type_exceptions s in
  (* Third pass: re-type statements *)
  let tprog = do_retype tprog in
  ok ({ s with tprog }, tprog)
