open Core

open Eformula
open Lex
open Elex
open Clex

module I = Info
module P = TTerm.PosTypeInfo

let debug_compiler = ref false
let debug msg = if !debug_compiler then Errors.debug_print ~f_name:(Some "compiler.ml") msg else ignore msg

(* TODO: constants inside of predicates do not
   actually introduce an unnamed variable for the
   "exception" predicate...
   i.e. being able to create a fresh name for variables
   is not needed*)
let c = ref 0
let fresh_var () = incr c; "_v" ^ string_of_int !c


let rec merge tts tts' =
  match tts, tts' with
  | [], _ -> tts'
  | tt :: tts, tt' :: tts' when Dom.equal_tt tt tt' -> tt :: (merge tts tts')
  | tt :: tts, tts' -> tt :: (merge tts tts')

let merge_all =
  List.fold_left ~init:[] ~f:merge

let normalize kvss =
  List.sort kvss ~compare:(fun (k, _) (k', _) -> String.compare k k')

let compile_tt = function
  | Dom.TInt -> Dom.TInt
  | TStr -> TStr
  | TFloat -> TFloat
  | TBool -> TInt
  | TTime -> TInt
  | TSpan -> TInt
  | TMoney _ -> TInt

let compile_dom = function
  | Dom.Int i -> Dom.Int i
  | Str s -> Str s
  | Float f -> Float f
  | Bool b -> Int (if b then 1 else 0)
  | Time t -> Int (MFOTL_lib.Time.to_int t)
  | Span s -> Int (MFOTL_lib.Time.Span.max_seconds s)
  | Money (Money.M (a, _)) -> Int a

let prefix_tt = function
  | Dom.TInt -> "i"
  | TStr -> "s"
  | TFloat -> "f"
  | _ -> assert false

let compile_epattern ?(use_pattern_for_enf=false) ?(only_pattern=false) ?(enftype=Enftype.causable) (f: Eformula.t) =
  let open Eformula in
  let module I = Eformula.Info in
  function
  | Pattern.PPresent -> f
  | PEventually i -> make (eventually i f) { I.dummy with enftype; flag_opt = Some (Interval.is_bounded i) }
  | PAlways i -> make (always i f) { I.dummy with enftype; flag_opt = Some (Interval.is_bounded i) }
  | PUntil (i, g) -> 
     if use_pattern_for_enf then
       make (until LR i g f) { I.dummy with enftype; flag_opt = Some (Interval.is_bounded i) }
     else if only_pattern then
       make (until L i g f) { I.dummy with enftype; flag_opt = Some (Interval.is_bounded i) }
     else
       make (until R i g f) { I.dummy with enftype; flag_opt = Some (Interval.is_bounded i) }
  | POnce i -> make (once i f) { I.dummy with enftype }
  | PHistorically i -> make (historically i f) { I.dummy with enftype }
  | PSince (i, g) ->
     if use_pattern_for_enf then
       make (since LR i f g) { I.dummy with enftype }
     else if only_pattern then
       make (since R i f g) { I.dummy with enftype }
     else
       make (since L i f g) { I.dummy with enftype }

let compile_eformulas ~f fs = f fs

let compile_epformula ?(use_pattern_for_enf=false) ?(only_pattern=false) ?(enftype=Enftype.causable) ~f (epf: Pattern.t): Eformula.t =
  map_consts ~f:compile_dom 
    (compile_epattern ~use_pattern_for_enf ~only_pattern ~enftype (compile_eformulas ~f epf.fs) epf.patt)

let compile_ex_neg ?(enftype_opt=None) vars ex =
  let enftype_neg_opt = Option.map ~f:Enftype.neg enftype_opt in
  match enftype_opt, enftype_neg_opt with
  | Some enftype, Some enftype_neg -> 
     List.map ex ~f:(fun x -> let vars = Set.elements (Set.diff (fv x) vars) in
                              let x = tbigexists ~enftype_opt:(Some enftype_neg) vars x in
                              make (neg x) { I.dummy with enftype; pos = x.info.pos })
  | _ ->
     List.map ex ~f:(fun x -> let vars = Set.elements (Set.diff (fv x) vars) in
                              let x = tbigexists vars x in
                              make (neg x) { I.dummy with pos = x.info.pos })

let compile_sc ?(enftype_opt=None) vars sc =
  match enftype_opt with
  | Some enftype -> 
     List.map sc ~f:(fun x -> let vars = Set.elements (Set.diff (fv x) vars) in
                              tbigexists ~enftype_opt:(Some enftype) vars x )
  | _ ->
     List.map sc ~f:(fun x -> let vars = Set.elements (Set.diff (fv x) vars) in
                              tbigexists vars x)

let sup_conj_ex_neg_and_scope side cpf f ex_neg sc =
  let ex_neg_and_scope = ex_neg @ sc in
  if not (List.is_empty ex_neg_and_scope) then
    make (conjs side [cpf; f ex_neg sc]) { I.dummy with enftype = Enftype.suppressable }
  else
    cpf

let compile_lhs ?(sup_constr=None) ?(cau_constr=None) vars (enftype: Enftype.t) pf ex sc =
  match Enftype.is_causable enftype, Enftype.is_suppressable enftype with
  | true, _ ->
    let enf_cau = Option.value_exn cau_constr in
    begin match enf_cau with
    | EClhsAll enf_pformula_cau ->
       let ex_neg = compile_ex_neg ~enftype_opt:(Some Enftype.causable) vars ex in
       let sc = compile_sc ~enftype_opt:(Some Enftype.causable) vars sc in
       let f = begin match enf_pformula_cau with
         | ECpfFormulas -> compile_epformula ~f:tbigcauconj pf
         | ECpfPformula -> compile_epformula ~use_pattern_for_enf:true ~f:tbigcauconj pf
         | ECpfPattern -> compile_epformula ~use_pattern_for_enf:true ~only_pattern:true ~f:tbignonconj pf
       end in
       tbigcauconj (f :: ex_neg @ sc)
    end
  | _, true ->
    let enf_sup = Option.value_exn sup_constr in
    begin match enf_sup with
    | ESlhsSPformula enf_pformula_sup ->
       (*print_endline (Pattern.to_string pf);*)
      begin match enf_pformula_sup with
      | ESpfFormula i ->
        let cpf = compile_epformula ~enftype:Enftype.suppressable ~f:(tbigsupconj i) pf in (* this is used for enforcement *)
        let ex_neg = compile_ex_neg vars ex in
        let sc = compile_sc vars sc in
        sup_conj_ex_neg_and_scope L cpf (fun ex_neg sc -> tbignonconj (ex_neg @ sc)) ex_neg sc
      | ESpfPformula i ->
        let cpf = compile_epformula ~use_pattern_for_enf:true ~f:(tbigsupconj i) pf in
        let ex_neg = compile_ex_neg ~enftype_opt:(Some Enftype.suppressable) vars ex in
        let sc = compile_sc vars sc in
        sup_conj_ex_neg_and_scope L cpf (fun ex_neg sc -> tbignonconj (ex_neg @ sc)) ex_neg sc 
      | ESpfPattern ->
         let cpf = compile_epformula ~use_pattern_for_enf:true ~only_pattern:true ~f:tbignonconj pf in
         let ex_neg = compile_ex_neg ~enftype_opt:(Some Enftype.suppressable) vars ex in
         let sc = compile_sc vars sc in
         sup_conj_ex_neg_and_scope L cpf (fun ex_neg sc -> tbignonconj (ex_neg @ sc)) ex_neg sc
      end
    | ESlhsCException i ->
      let cpf = compile_epformula ~f:tbignonconj pf in
      let ex_neg = compile_ex_neg ~enftype_opt:(Some Enftype.suppressable) vars ex in
      let sc = compile_sc vars sc in
      sup_conj_ex_neg_and_scope R cpf
        (fun ex_neg sc ->
          let ex_neg_sup = tbigsupconj i ex_neg in
          make (conjs L (ex_neg_sup::sc)) { I.dummy with enftype = Enftype.suppressable })
          ex_neg sc
    | ESlhsSScope i ->
       let cpf = compile_epformula ~f:tbignonconj pf in
       let ex_neg = compile_ex_neg vars ex in
       let sc = compile_sc  ~enftype_opt:(Some Enftype.suppressable)  vars sc in
       sup_conj_ex_neg_and_scope R cpf
         (fun ex_neg sc ->
           let sc_sup = tbigsupconj i sc in
           make (conjs L (sc_sup::ex_neg)) { I.dummy with enftype = Enftype.suppressable })
         ex_neg sc
    end
  | _ ->
    let f = compile_epformula ~f:tbignonconj pf in
    let ex_neg = compile_ex_neg vars ex in
    let sc = compile_sc vars sc in
    tbignonconj (f :: ex_neg @ sc)

let rec compile_typeterm = function
  | TypeTerm.TConst d   -> ["", d]
  | TNamed          tn  -> raise (Invalid_argument ("Cannot compile TName " ^ tn))
  | TVar            tv  -> raise (Invalid_argument ("Cannot compile TVar " ^ tv))
  | TSum            kvs -> let f (k, v) =
                             List.map (compile_typeterm v) ~f:(Util.concat k) in
                           List.concat (List.map kvs ~f)

let compile_eval_default aliases typeterm =
  List.map ~f:(fun (name, typ_alias) -> (name, compile_tt typ_alias))
    (compile_typeterm (TypeTerm.eval_aliases_default aliases
                         (TypeTerm.TConst TInt) (TypeTerm.unalias aliases typeterm)))


let compile_let_binding aliases (f: Eformula.t) (pred: Eformula.t) : string * (ident * Dom.tt option) list * Eformula.t =
  match pred with
  | { form = Predicate (p_name, trms); _ } ->
    let process_term fs (t: ETerm.t) = match t.trm with
      | ETerm.Var v ->
         (*print_endline ("process_term " ^ v ^ " " ^ TypeTerm.to_string t.info.typ);*)
         fs, (v, compile_eval_default aliases t.info.typ)
      | _ ->
         let w = fresh_var () in
         let v = ETerm.{ trm = var w;
                         info = { P.dummy with typ = t.info.typ } } in
         let ef = match t.trm with
           | Const c -> Eformula.{ form = eqconst v c;
                                   info = { I.dummy with enftype = Enftype.obs } }
           | _ -> 
             let eq = ETerm.{ trm = binop v ETerm.Bop.BEq t;
                              info = { P.dummy with typ = TypeTerm.TConst Dom.TBool } } in
             Eformula.{ form = eqconst eq (Dom.Bool true);
                        info = { I.dummy with enftype = Enftype.obs } } in
         ef :: fs, (w, compile_eval_default aliases t.info.typ)
    in
    let bvs = Set.of_list (module String) (ETerm.fv_list trms) in
    let fs', trms_list = List.fold_map trms ~init:[] ~f:process_term in
    let trms = List.concat_map trms_list ~f:(
                   fun (v, l) -> List.map l ~f:(fun (w, tt) -> Util.concat v (w, Some tt))) in
    let fs = f :: List.rev fs' in
    let compile_exists f =
      let fvs = Set.elements (Set.diff (Eformula.fv f) bvs) in
      List.fold_left fvs ~init:f ~f:(fun f x -> Eformula.make (Eformula.exists x f) f.info) in
    let fs = List.map fs ~f:compile_exists in
    let rhs = tbigcauconj fs in
    (p_name, trms, rhs)
  | _ -> assert false

let compile_renaming form renaming =
  let f (x, y) form =
    if ETerm.is_var y then
      Eformula.subst (Map.of_alist_exn (module String) [ETerm.unvar y, x]) form
    else
      let s =
        match Enftype.is_causable form.info.enftype,
              Enftype.is_suppressable form.info.enftype with
        | false, false -> Side.N
        | false, true -> L
        | true, _ -> assert false in
      Eformula.make (Eformula.conj s form (Eformula.make (Eformula.eqconst x (ETerm.unconst y)) form.info)) form.info in
  List.fold_right renaming ~init:form ~f

let compile_exists f vars =
  List.fold_right vars ~init:f ~f:(fun x f -> Eformula.make (Eformula.exists x f) f.info)

let compile_edisjunct ?(cau_constr=None) ?(sup_constr=None) vars (enftype: Enftype.t) ed: Eformula.t =
  (* let renaming = List.map2 ed.params_new ed.params_original ~f:(fun t1 t2 -> eeqconst t1 t2) in *)
  (* TODO: implement variable renaming using 'gets' operator *)
  let compiled = 
    match Enftype.is_causable enftype, Enftype.is_suppressable enftype with
    | true, _ -> 
       let c = Option.value_exn cau_constr in
       compile_lhs ~cau_constr:(Some c) vars Enftype.causable ed.pf ed.exceptions ed.scopes
    | _, true ->
       let c = Option.value_exn sup_constr in
       compile_lhs ~sup_constr:(Some c) vars Enftype.suppressable ed.pf ed.exceptions ed.scopes
    | _  ->
      compile_lhs vars Enftype.obs ed.pf ed.exceptions ed.scopes
(*let ex_neg = List.map ed.exceptions
                      ~f:(fun x -> make (neg x) { I.dummy with pos = x.info.pos }) in
       tbignonconj (compile_epformula ~f:(tbignonconj) ed.pf :: ex_neg @ ed.scopes)**)
  in
  let renaming = List.zip_exn ed.params_new ed.params_original in
  let compiled = compile_renaming compiled renaming in
  let bvs = Set.elements (Set.diff (Eformula.fvs [compiled])
                            (Set.of_list (module String) (List.map ~f:ETerm.unvar ed.params_new))) in
  debug (Eformula.to_string compiled);
  debug (String.concat ~sep:"," bvs);
  compile_exists compiled bvs

let fv_of_ecrule = function
  | ECImplication (_, _, _, pf1, _, _, pf2, _, _, _) ->
     Set.union_list (module StringVar) Elex.Pattern.[fv pf1; fv pf2](*; fvs ex; fvs sc]*)
  | ECDefinitionRef (_, _, _, pf, _, _, _, _, _, _) ->
     Set.union_list (module StringVar) Elex.Pattern.[fv pf](*; fvs ex; fvs sc]*)
  | ECDefinitionDis (disjuncts, _, _, _) ->
     Set.union_list (module StringVar)
       (List.concat_map (Map.data disjuncts) ~f:(
            fun disjunct ->
            Elex.Pattern.[fv disjunct.pf](*; fvs disjunct.exceptions; fvs disjunct.scopes]*)))

let compile_let_rule aliases = function
  | ECDefinitionRef (_, _, _, pf, ex, sc, _, g, enftype, enf_constr) as r ->
     begin
       let vars = fv_of_ecrule r in
       match enf_constr with
       | Some (ESd enf_sup_lhs) ->
          let f = compile_lhs ~sup_constr:(Some enf_sup_lhs) vars Enftype.suppressable pf ex sc in
          compile_let_binding aliases f g
       | Some (ECd enf_cau_lhs) ->
          let f = compile_lhs ~cau_constr:(Some enf_cau_lhs) vars Enftype.causable pf ex sc in
          compile_let_binding aliases f g
       | None ->
         let f = compile_lhs vars Enftype.obs pf ex sc in
         print_endline ("g = " ^ Eformula.to_string g);
         print_endline (Elex.Pattern.to_string pf);
         (match compile_let_binding aliases f g with (_, _, f) ->          print_endline ("-> " ^ Eformula.to_string f););
         (*let pf_comp = compile_epformula ~f:(tbignonconj) pf in
           let f = tbignonconj (pf_comp :: ex_neg @ sc) in*)

         compile_let_binding aliases f g
         (*let ex_neg = List.map ex ~f:(fun x -> make (neg x) { I.dummy with pos = x.info.pos }) in
          let pf_comp = compile_epformula ~f:(tbignonconj) pf in
          let f = tbignonconj (pf_comp :: ex_neg @ sc) in
           compile_let_binding aliases f g*)
     end, enftype
  | ECDefinitionDis (edisjuncts, g, enftype, enf_constr) (*as r*) ->
     begin
       (*let vars = fv_of_ecrule r in*)
       match enf_constr with
    | Some (ECdd (idx, enf_cau_lhs)) -> 
      let rhs_list =
        let aux ~key:j ~data:d =
          let vars = Elex.Pattern.fv d.pf in
          if idx = j then
            compile_edisjunct ~cau_constr:(Some enf_cau_lhs) vars Enftype.causable d
          else
            compile_edisjunct vars Enftype.bot d
        in
        Map.mapi edisjuncts ~f:aux |> Map.data
      in
      let rhs = tbigcaudisj idx rhs_list in
      compile_let_binding aliases rhs g
    | Some (ESdd enf_sup_lhs_list) ->
      let rhs = tbignondisj (
          List.map2_exn (Map.data edisjuncts) enf_sup_lhs_list
            ~f:(fun d c -> let vars = Elex.Pattern.fv d.pf in
                 compile_edisjunct ~sup_constr:(Some c) vars Enftype.suppressable d)) in
      compile_let_binding aliases rhs g
    | None ->
      let rhs = tbignondisj (Map.data (Map.map edisjuncts ~f:(fun d ->
          let vars = Elex.Pattern.fv d.pf in compile_edisjunct vars Enftype.bot d))) in
      compile_let_binding aliases rhs g
    end, enftype
  | _ -> assert false

let compile_imp (f1: Eformula.t) (f2: Eformula.t) (s: Side.t) (label_opt: string option) =
  let vars_forall = Set.elements (fv f2) in
  let vars_exists = Set.elements (Set.diff (fv f1) (fv f2)) in
  let cau = { I.dummy with enftype = Enftype.causable } in
  let f = (tbigcauforall vars_forall
             (make (imp s (tbigexists vars_exists f1) f2)
                cau )) in
  let f = match label_opt with
    | None -> f
    | Some s -> make (label s f) cau
  in make (always Interval.full f) cau
                   
let compile_imp_rule label = function
  | ECImplication (_, _, info, pf1, ex, sc, pf2, _, _, Some enf_info) as r ->
     begin
       let vars = fv_of_ecrule r in
       (*print_endline ("pf1: " ^ Elex.Pattern.to_string pf1);
       print_endline ("pf2: " ^ Elex.Pattern.to_string pf2);
         print_endline ("vars: " ^ String.concat ~sep:"," (Set.elements vars));*)
       let label_opt = if label then Some (LexingInfo.to_string info) else None in
       match enf_info with
       | ESciLhs enf_sup ->
         let lhs = compile_lhs ~sup_constr:(Some enf_sup) vars Enftype.suppressable pf1 ex sc in
         (*print_endline (Eformula.to_string lhs);*)
         let rhs = compile_epformula ~f:tbignonconj pf2 in
         compile_imp lhs rhs L label_opt
       | ECciRhs enf_cau ->
          let lhs = compile_lhs vars Enftype.obs pf1 ex sc in
          (*print_endline (Eformula.to_string lhs);*)
          begin match enf_cau with
          | ECpfFormulas ->
             let rhs = compile_epformula ~f:tbigcauconj pf2 in
             compile_imp lhs rhs R label_opt
          | ECpfPformula ->
             let rhs = compile_epformula ~use_pattern_for_enf:true ~f:tbigcauconj pf2 in
             compile_imp lhs rhs R label_opt
          | ECpfPattern ->
             let rhs = compile_epformula ~use_pattern_for_enf:true ~only_pattern:true ~f:tbignonconj pf2 in
             compile_imp lhs rhs R label_opt
          end
    end
  | _ ->  assert false

let compile_events events aliases =
  let f (_, (_, _, (_, itl), _)) = not itl in
  let event_list = List.filter ~f (Map.to_alist events) in
  let compile_event (name, (event_type, args, (enftype, _), _)) =
    let type_args (name, typ_alias) =
      let terms = compile_eval_default aliases typ_alias in
      terms |>
        List.map ~f:(Util.concat name) |>
        List.map ~f:(fun (name, typ_alias) -> (name, compile_tt typ_alias))
    in
    let typed_args = List.concat (List.map args ~f:type_args) in
    CEvent (name, event_type, enftype, typed_args) (* TODO: which polarity value should be used? *)
  in
  List.map event_list ~f:compile_event

let compile_functions functions aliases =
  let function_list = Map.to_alist functions in
  let compile_function (name, (typed_args, return_type, _)) =
    let type_args (name, typ_alias) =
      let terms = compile_eval_default aliases typ_alias in
      terms |>
        List.map ~f:(Util.concat name) |>
        List.map ~f:(fun (name, typ_alias) -> (name, compile_tt typ_alias))
    in
    let typed_args = List.concat (List.map typed_args ~f:type_args) in
    let return_type = compile_eval_default aliases return_type in
    match return_type with
    | [_, d] -> CFunction (name, typed_args, d)
    | _ -> raise (Invalid_argument ("Cannot compile function " ^ name ^ ": complex return type"))
  in
  List.map function_list ~f:compile_function

let is_exception = function
  | ECDefinitionRef (_, TRTException, _, _, _, _, _, _, _, _) -> true
  | ECDefinitionRef (_, TRTExceptionC, _, _, _, _, _, _, _, _) -> true
  | _ -> false

let is_scope = function
  | ECDefinitionRef (_, TRTScope, _, _, _, _, _, _, _, _) -> true
  | _ -> false

let predicate_from_definition = function
  | ECDefinitionRef (idx, _, _, _, _, _, _, g, _, _) -> (idx, g)
  | _ -> assert false

let compile_signature _ events functions aliases _ _ =
  let event_signatures = compile_events events aliases in
  let function_signatures = compile_functions functions aliases in
  List.concat [event_signatures; function_signatures]

let is_let_rule = function
  | ECDefinitionRef _
  | ECDefinitionDis _ -> true
  | _ -> false

let is_imp_rule = function
  | ECImplication _ -> true
  | _ -> false

let is_vanilla = function
  | ECImplication (_, _, _, _, _, _, _, Vanilla, _, _) -> true
  | ECImplication (_, _, _, _, _, _, _, Assumed, _, _) -> true
  | _ -> false

let compile (eprog:Elex.eprog) (unroll: bool) (label: bool) : Clex.cprog =
  (*print_endline (string_of_eprog eprog);*)
  let sorted_c_rules_opt = List.map eprog.compilation_order ~f:(Map.find eprog.ecrules) in
  let sorted_c_rules     = List.filter_map ~f:(fun x -> x) sorted_c_rules_opt in
  let let_rules          = List.filter sorted_c_rules ~f:is_let_rule in
  let imp_rules          = List.filter sorted_c_rules ~f:is_imp_rule in
  let non_vanilla        = List.filter imp_rules ~f:(fun r -> not (is_vanilla r)) in
  if List.is_empty non_vanilla then
    Errors.warn "No obligation rules are marked as (transparently) enforceable, compiled formula will be a tautology" None;
  debug (Printf.sprintf "Non-vanilla rules: %d" (List.length non_vanilla));
  let formulae = List.map non_vanilla ~f:(compile_imp_rule label) in
  let let_bindings = List.map let_rules ~f:(compile_let_rule eprog.ealiases) in
  let phi = List.fold_right let_bindings ~f:(
                fun ((p_name, vars, rhs), enftype) phi ->
                Eformula.make (Eformula.flet p_name (Some enftype) vars rhs phi)
                  { I.dummy with enftype = Enftype.cau } 
              ) ~init:(tbigcauconj formulae) in
  let phi = if unroll then Eformula.unprime (Eformula.unroll_let phi) else phi in
  let signature = compile_signature eprog.pols eprog.eevents eprog.efunctions eprog.ealiases
      eprog.rule_ctxts let_rules in
  print_endline (Eformula.to_string phi);
  { signature; phi }
