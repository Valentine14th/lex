open Base
open Tlex
open Tformula
open TTerm

open Z3

module Time = MFOTL_lib.Time
module Interval = MFOTL_lib.Interval

let debug_smt = ref false
let debug msg = if !debug_smt then Errors.debug_print ~f_name:(Some "smt.ml") msg

(* Embedding in FOL *)

let tint = TypeTerm.TConst Dom.TInt
let tbool = TypeTerm.TConst Dom.TBool

let info_int  = { PosTypeInfo.dummy with typ = tint }
let info_bool = { PosTypeInfo.dummy with typ = tbool }

module FOL_State = struct
  
  type u =
    {
      ev: int;
      tp: int;
    }

  let empty = { ev = 0; tp = 0 }

  let var_tp u = Printf.sprintf "tp.%d" u.tp
  let tp u = TTerm.make (TTerm.Var (var_tp u)) info_int

  let ts u = TTerm.make (TTerm.App ("~ts", [tp u])) info_int
  let tpts u = [tp u; ts u]

  let new_event u =
    let e = Printf.sprintf "ev.%d" u.ev in
    e, { u with ev = u.ev + 1 }
  
  let inc_tp u = let u = { u with tp = u.tp + 1 } in u

  type 'a t = 'a * u

end

let rec to_fol_core_ ((f:Tformula.t),  u) : Tformula.core_t * FOL_State.u =
  let open FOL_State in
  let lb itv u u' =
    if Time.Span.is_zero (Interval.left itv) then
      []
    else
      [Tformula.make_dummy (
           EqConst (TTerm.make (
                        TTerm.Binop
                          (TTerm.make (TTerm.Binop (ts u, Term.Bop.BSub, ts u')) info_int,
                           Term.Bop.BGeq,
                           TTerm.dummy_int (Time.Span.min_seconds (Interval.left itv))))
                      info_bool,
                    Dom.bool_tt))] in
  let ub itv u u' =
    match Interval.right itv with
    | Some r ->
       [Tformula.make_dummy (
           EqConst (TTerm.make (
                        TTerm.Binop
                          (TTerm.make (TTerm.Binop (ts u, Term.Bop.BSub, ts u')) info_int,
                           Term.Bop.BLeq,
                           TTerm.dummy_int (Time.Span.min_seconds r)))
                      info_bool,
                    Dom.bool_tt))]
    | None -> [] in
  let lt u u' =
    Tformula.make_dummy (
        EqConst (TTerm.make (TTerm.Binop (tp u, Term.Bop.BLt, tp u')) info_bool, Dom.bool_tt)) in
  let leq u u' =
    Tformula.make_dummy (
        EqConst (TTerm.make (TTerm.Binop (tp u, Term.Bop.BLeq, tp u')) info_bool, Dom.bool_tt)) in
  let old v = { v with tp = u.tp } in
  match f.form with 
  | TT ->
     TT, u
  | FF ->
     FF, u
  | EqConst (x, v) ->
     EqConst (x, v), u
  | Predicate (e, t) ->
     Predicate (e, tp u :: t), u
  | Predicate' (_, _, f) ->
     let f, u = to_fol_ (f, u) in
     f.form, u
  | Let _ -> assert false
  | Let' (_, _, _, _, g) ->
     let g, u = to_fol_ (g, u) in
     g.form, u
  | Agg (s, _, _, y, _) ->
     let e, u = new_event u in
     Predicate (e, (tpts u) @ (List.map ~f:TTerm.dummy_var (s :: y))), u
  | Top (s, _, _, y, _) ->
     let e, u = new_event u in
     Predicate (e, (tpts u) @ (List.map ~f:TTerm.dummy_var (s @ y))), u
  | Neg f ->
     let f, u = to_fol_ (f, u) in
     Neg f, u
  | And (s, fs) ->
     let f g (fs, u) = let f, u = to_fol_ (g, u) in (f :: fs, old u) in
     let fs, u = List.fold_right fs ~init:([], u) ~f in
     And (s, fs), u
  | Or (s, fs) ->
     let f g (fs, u) = let f, u = to_fol_ (g, u) in (f :: fs, old u) in
     let fs, u = List.fold_right fs ~init:([], u) ~f in
     Or (s, fs), u
  | Imp (s, f, g) ->
     let f, u = to_fol_ (f, u) in
     let g, u = to_fol_ (g, old u) in
     Imp (s, f, g), old u
  | Exists (x, f) ->
     let f, u = to_fol_ (f, u) in
     Exists (x, f), old u
  | Forall (x, f) ->
     let f, u = to_fol_ (f, u) in
     Forall (x, f), old u
  | Prev (itv, f) ->
     (* TODO: Check the use of min_seconds, max_seconds here *)
     let u' = inc_tp u in
     let f, u'' = to_fol_ (f, u') in
     let c = Tformula.make_dummy (
                 EqConst (
                     TTerm.make
                       (TTerm.Binop
                          (tp u',
                           Term.Bop.BEq,
                           TTerm.make
                             (TTerm.Binop
                                (tp u,
                                 Term.Bop.BSub,
                                 TTerm.make
                                   (TTerm.Const (Dom.Int 1))
                                   { PosTypeInfo.dummy with typ = TypeTerm.TConst Dom.TInt } ))
                             { PosTypeInfo.dummy with typ = TypeTerm.TConst Dom.TInt }))
                       { PosTypeInfo.dummy with typ = TypeTerm.TConst Dom.TBool },
                     Dom.bool_tt) ) in
     let d = lb itv u u' in
     let e = ub itv u u' in
     Exists (var_tp u', Tformula.make_dummy (And (Side.N, [f; c] @ d @ e))),
     u''
  | Next (itv, f) ->
     let u' = inc_tp u in
     let f, u'' = to_fol_ (f, u') in
     let c = Tformula.make_dummy (
                 EqConst (
                     TTerm.make
                       (TTerm.Binop
                          (tp u',
                           Term.Bop.BEq,
                           TTerm.make
                             (TTerm.Binop
                                (tp u,
                                 Term.Bop.BAdd,
                                 TTerm.make
                                   (TTerm.Const (Dom.Int 1))
                                   { PosTypeInfo.dummy with typ = TypeTerm.TConst Dom.TInt } ))
                             { PosTypeInfo.dummy with typ = TypeTerm.TConst Dom.TInt }))
                       { PosTypeInfo.dummy with typ = TypeTerm.TConst Dom.TBool },
                     Dom.bool_tt) ) in
     let d = lb itv u' u in
     let e = ub itv u' u in
     Exists (var_tp u', Tformula.make_dummy (And (Side.N, [f; c] @ d @ e))),
     u''
  | Once (itv, f) ->
     let u' = inc_tp u in
     let f, u'' = to_fol_ (f, u') in
     let d = lb itv u u' in
     let e = ub itv u u' in
     let h = leq    u' u in
     Exists (var_tp u', Tformula.make_dummy (And (Side.N, f :: h :: d @ e))),
     u''
  | Eventually (itv, f) ->
     let u' = inc_tp u in
     let f, u'' = to_fol_ (f, u') in
     let d = lb itv u' u in
     let e = ub itv u' u in
     let h = leq    u u' in
     Exists (var_tp u', Tformula.make_dummy (And (Side.N, f :: h :: d @ e))),
     u''
  | Historically (itv, f) ->
     let u' = inc_tp u in
     let f, u'' = to_fol_ (f, u') in
     let d = lb itv u u' in
     let e = ub itv u u' in
     let h = leq    u' u in
     Forall (var_tp u',
             Tformula.make_dummy
               (Imp (Side.N, Tformula.make_dummy (And (Side.N, h :: d @ e)), f))),
     u''
  | Always (itv, f) ->
     let u' = inc_tp u in
     let f, u'' = to_fol_ (f, u') in
     let d = lb itv u' u in
     let e = ub itv u' u in
     let h = leq    u u' in
     Forall (var_tp u',
             Tformula.make_dummy
               (Imp (Side.N, Tformula.make_dummy (And (Side.N, h :: d @ e)), f))),
     u''
  | Since (_, itv, f, g) ->
     let u' = inc_tp u in
     let u'' = inc_tp u' in
     let f, u''' = to_fol_ (f, u'') in
     let g, u''' = to_fol_ (g, u''') in
     let d  = lb itv u u' in
     let e  = ub itv u u' in
     let h  = leq    u' u in
     let h' = leq    u'' u in
     let i  = lt     u' u'' in
     let phi = Tformula.make_dummy
                 (Forall (var_tp u'',
                          Tformula.make_dummy
                            (Imp (Side.N, Tformula.make_dummy (And (Side.N, [h'; i])), f)))) in
     Exists (var_tp u', Tformula.make_dummy (And (Side.N, g :: h :: d @ e @ [phi]))),
     u'''
  | Until (_, itv, f, g) ->
     let u' = inc_tp u in
     let u'' = inc_tp u' in
     let f, u''' = to_fol_ (f, u'') in
     let g, u''' = to_fol_ (g, u''') in
     let d  = lb itv u' u in
     let e  = ub itv u' u in
     let h  = leq    u u' in
     let h' = leq    u u'' in
     let i  = lt     u'' u' in
     let phi = Tformula.make_dummy
                 (Forall (var_tp u'',
                          Tformula.make_dummy
                            (Imp (Side.N, Tformula.make_dummy (And (Side.N, [h'; i])), f)))) in
     Exists (var_tp u', Tformula.make_dummy (And (Side.N, g :: h :: d @ e @ [phi]))),
     u'''
  | Type _ ->
     TT, u

and to_fol_ (f, u) =
  let f = Tformula.unroll_let f in
  let form, u = to_fol_core_ (f, u) in
  Tformula.{ f with form }, u

let to_fol (f : Tformula.t) : Tformula.t  = fst (to_fol_ (f, FOL_State.empty))

let tt_to_sort ctx =
  function
  | Dom.TInt
    | Dom.TTime
    | Dom.TSpan    -> Z3.Arithmetic.Integer.mk_sort ctx
  | Dom.TStr       -> Seq.mk_string_sort ctx
  | Dom.TFloat
    | Dom.TMoney _ -> FloatingPoint.mk_sort_double ctx
  | Dom.TBool      -> Boolean.mk_sort ctx

let ttt_to_sort ctx =
  function
  | TypeTerm.TConst tt -> tt_to_sort ctx tt
  | TNamed tn
    | TVar tn -> Sort.mk_uninterpreted_s ctx tn
  | _ -> assert false

let dom_to_expr ctx =
  function
  | Dom.Int i -> Arithmetic.Integer.mk_numeral_i ctx i
  | Str s -> Seq.mk_string ctx s
  | Float f -> FloatingPoint.mk_numeral_f ctx f (tt_to_sort ctx Dom.TFloat)
  | Bool true -> Boolean.mk_true ctx
  | Bool false -> Boolean.mk_false ctx
  | Time t -> Arithmetic.Integer.mk_numeral_i ctx (MFOTL_lib.Time.to_int t)
  | Span t -> Arithmetic.Integer.mk_numeral_i ctx (MFOTL_lib.Time.Span.min_seconds t)
  | Money m -> FloatingPoint.mk_numeral_f ctx (Money.amount m) (tt_to_sort ctx Dom.TFloat)

let make_func_decl aliases ctx s arg_terms ret_term =
  let arg_ttts = List.map ~f:(fun t -> TypeTerm.unalias aliases t.info.typ) arg_terms in
  let arg_sorts = List.map ~f:(ttt_to_sort ctx) arg_ttts in
  let ret_ttt = TypeTerm.unalias aliases ret_term.info.typ in
  let ret_sort = ttt_to_sort ctx ret_ttt in
  let suffix = String.concat ~sep:"_" (List.map ~f:TypeTerm.to_string (arg_ttts @ [ret_ttt])) in
  FuncDecl.mk_func_decl_s ctx (s ^ "_" ^ suffix) arg_sorts ret_sort

let rec term_to_expr
          aliases
          (bruijn : (string * Z3.Sort.sort) list)
          ctx (trm : TTerm.t) : Z3.Expr.expr =
  let aux = term_to_expr aliases bruijn ctx in
  let open Z3 in
  match trm.trm with
  | Var x ->
     let x_ident = Term.StringVar.ident x in
     (match List.findi bruijn ~f:(fun _ (y, _) -> String.equal y x_ident) with
      | Some (i, (_, sort)) -> Quantifier.mk_bound ctx i sort
      | None -> (*debug ("Free variable: " ^ x);
                debug ("term: " ^ TTerm.to_string trm);
                debug ("t_vars: " ^ String.concat ~sep:", " (List.map ~f:(fun (y, ttt) -> y ^ " -> " ^ TypeTerm.to_string ttt) t_vars));*)
                let sort = ttt_to_sort ctx trm.info.typ in
                Expr.mk_const_s ctx x sort)
  | Const d ->
     dom_to_expr ctx d
  | App (f, ts) ->
     let func_decl = make_func_decl aliases ctx f ts trm in
     Expr.mk_app ctx func_decl (List.map ~f:aux ts)
  | Unop (o, t) ->
     let func_decl = make_func_decl aliases ctx ("uop:" ^ Term.Uop.to_string o) [t] trm in
     Expr.mk_app ctx func_decl [aux t]
  | Binop (t, o, t') ->
     let e  = aux t in
     let e' = aux t' in
     (* TODO: add arithmetic operators *)
     (match o with
      | Term.Bop.BLeq -> Arithmetic.mk_le ctx e e'
      | Term.Bop.BLt  -> Arithmetic.mk_lt ctx e e'
      | Term.Bop.BGeq -> Arithmetic.mk_ge ctx e e'
      | Term.Bop.BGt  -> Arithmetic.mk_gt ctx e e'
      | Term.Bop.BAdd -> Arithmetic.mk_add ctx [e; e']
      | Term.Bop.BSub -> Arithmetic.mk_sub ctx [e; e']
      | Term.Bop.BMul -> Arithmetic.mk_mul ctx [e; e']
      | Term.Bop.BDiv -> Arithmetic.mk_div ctx e e'
      | _ -> let func_decl = make_func_decl aliases ctx ("bop:" ^ Term.Bop.to_string o) [t; t'] trm in
             Expr.mk_app ctx func_decl [e; e']
     )
  | _ -> (*TODO: Record types*) assert false

let find_ident_type (x: string) (form: Tformula.t) =
  let terms = Tformula.terms form in
  let is_same_ident trm = match trm.trm with
    | Var v -> String.equal v x
    | _ -> false in
  match Core.Set.find terms ~f:is_same_ident with
  | Some trm -> trm.info.typ
  | _ -> TConst Dom.TInt

let rec to_expr_ aliases bruijn ctx (form : Tformula.t) : Z3.Expr.expr =
  let aux = to_expr_ aliases bruijn ctx in
  let open Z3 in
  (*debug ("to_expr_: " ^ Tformula.to_string form);*)
  match form.form with
  | TT ->
     Boolean.mk_true ctx
  | FF ->
     Boolean.mk_false ctx
  | EqConst (x, Dom.Bool true) ->
     term_to_expr aliases bruijn ctx x
  | EqConst (x, c) ->
     Boolean.mk_eq ctx (term_to_expr aliases bruijn ctx x) (dom_to_expr ctx c)
  | Predicate (e, ts) ->
     let func_decl = make_func_decl aliases ctx e ts (make (Const (Dom.Bool true)) info_bool) in
     Expr.mk_app ctx func_decl (List.map ~f:(term_to_expr aliases bruijn ctx) ts)
  | Neg f ->
     Boolean.mk_not ctx (aux f)
  | And (_, fs) ->
     Boolean.mk_and ctx (List.map ~f:aux fs)
  | Or (_, fs) ->
     Boolean.mk_or ctx (List.map ~f:aux fs)
  | Imp (_, f, g) ->
     Boolean.mk_implies ctx (aux f) (aux g)
  | Exists (x, f) ->
     let ttt = find_ident_type x f in
     let quant_type = TypeTerm.unalias aliases ttt in
     let quant_sort = ttt_to_sort ctx quant_type in
     let f = to_expr_ aliases ((x, quant_sort) :: bruijn) ctx f in
     let q = Quantifier.mk_exists ctx [quant_sort] [Symbol.mk_string ctx x] f None [] [] None None in
     Quantifier.expr_of_quantifier q
  | Forall (x, f) ->
     let ttt = find_ident_type x f in
     (*Stdio.print_endline (String.concat ~sep:", " (List.map ~f:(fun (k, v) -> k ^ " -> " ^ TypeTerm.ttt_to_string v) form.info.t_vars));*)
     let quant_type = TypeTerm.unalias aliases ttt in
     let quant_sort = ttt_to_sort ctx quant_type in
     let f = to_expr_ aliases ((x, quant_sort) :: bruijn) ctx f in
     let q = Quantifier.mk_forall ctx [quant_sort] [Symbol.mk_string ctx x] f None [] [] None None in
     Quantifier.expr_of_quantifier q
  | _ -> assert false

let to_expr ctx tprog f =
  let aliases = tprog.taliases in
  let f = to_fol f in
  debug ("FOL formula: " ^ Tformula.to_string f);
  to_expr_ aliases [] ctx f

let is_tautology tprog ?(assume=None) f =
  debug ("is_tautology: " ^ Tformula.to_string f);
  (*let tp_0 = Tformula.make (
                 Tformula.EqConst (make_dummy (Var "tp.0"), Dom.Int 0))
               { Tformula.Info.dummy with t_vars = [("tp.0", tint)] } in*)
  let ts_mono = Tformula.make_dummy (
                    Tformula.forall "tp.1" (
                        Tformula.make_dummy (
                            Tformula.forall "tp.2" (
                                Tformula.make_dummy (
                                    Tformula.imp N 
                                      (Tformula.make_dummy (EqConst (make (Binop (make (Var "tp.1") info_int,
                                                                            Term.Bop.BLeq,
                                                                            make (Var "tp.2") info_int))
                                                                  info_bool,
                                                       Dom.bool_tt)))
                                      ((Tformula.make_dummy (
                                            EqConst ((make (Binop (make (App ("~ts", [make (Var "tp.1") info_int])) info_int,
                                                                   Term.Bop.BLeq,
                                                                   make (App ("~ts", [make (Var "tp.2") info_int])) info_int))
                                                        info_bool),
                                                     Dom.bool_tt)))))
                              )
                          )
                      )
                  ) in
  let f = Tformula.make_dummy (Tformula.imp N ts_mono f) in
  debug ("MFOTL formula: " ^ Tformula.to_string f);
  let ctx = Z3.mk_context [] in
  let solver = Solver.mk_solver ctx None in
  let params = Z3.Params.mk_params ctx in
  Z3.Params.update_param_value ctx "timeout" !Util.z3_to;
  Z3.Solver.set_parameters solver params;
  let expr = to_expr ctx tprog f in
  let expr = match assume with
    | None -> expr
    | Some g -> Boolean.mk_implies ctx (to_expr ctx tprog g) expr in
  debug ("Z3 expression: " ^ Expr.to_string expr);
  let negated_expr = Boolean.mk_not ctx expr in
  Solver.add solver [negated_expr];
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> debug "Z3: unsatisfiable"; true
  | Solver.SATISFIABLE -> debug (Printf.sprintf "Z3: satisfiable with model %s" (Model.to_string (Option.value_exn (Solver.get_model solver)))); false
  | Solver.UNKNOWN -> debug "Z3: unknown"; false 

