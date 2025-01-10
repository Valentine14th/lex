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
  { s with tprog = Tlex.add_tstmt tstmt s.tprog }

let add_talias alias typ doc_string s pos =
  { s with tprog = Tlex.add_talias alias typ doc_string s.tprog pos }

let add_tfunction name arg_types return_type doc_string s pos =
  { s with tprog = Tlex.add_tfunction name arg_types return_type doc_string s.tprog pos }

let add_tevent event_type name args pol ds s (pos: LexingInfo.t) =
  { s with tprog = Tlex.add_tevent event_type name args pol ds s.tprog pos }

let add_vars i vs s =
  { s with tprog = Tlex.add_vars i vs s.tprog }

let add_rule pos rule_num label s =
  { s with tprog = Tlex.add_rule pos rule_num label s.tprog }

let add_section pos label s =
  { s with tprog = Tlex.add_section pos label s.tprog }

(* let add_exception_first_pass i f refs s = *)
let add_exception_first_pass i f (refs: Tlex.Ref.t list) s =
  { s with exceptions_first_pass = (i,f,refs)::s.exceptions_first_pass }

let add_scope_first_pass i f refs s =
  { s with scopes_first_pass = (i,f,refs)::s.scopes_first_pass}

let add_exception i f refs s =
  { s with tprog = Tlex.add_exception i f refs s.tprog; }

let add_scope i f refs s =
  { s with tprog = Tlex.add_scope i f refs s.tprog; }

let set_labels pos section_kind label s =
  let articles = match section_kind with
    | Article 0 ->
      let law_name = begin try Label.qualified_name_of_law ~exn:true s.label.law
                     with _ -> Errors.label_error ("Article \"" ^ fst label ^ "\" must be inside a law, but is not") pos 
        end in
      let articles = Map.find_multi s.articles law_name in
      if List.exists articles ~f:(String.equal (fst label)) then Errors.label_error ("Article \"" ^ fst label ^ "\" already exists in Law \"" ^ law_name ^ "\"") pos
      else Map.add_multi s.articles ~key:law_name ~data:(fst label)
    | _ -> s.articles
  in
  let l = Label.set pos section_kind label s.label in
  { s with label = l;
           tprog = Tlex.set_labels pos l s.tprog;
           articles = articles }

(* Visitors *)

let c = ref (-1) 
let fresh () = incr c; !c

let type_check_constant c t = match (c, t) with
  | Dom.Int _, Dom.TInt
  | Dom.Str _, TStr
  | Dom.Float _, TFloat
  | Dom.Bool _, TBool
  | Dom.Time _, TTime -> true
  | Dom.Money m, TMoney c -> String.equal (Money.currency m) c
  | _, _ -> false

let type_unot = function
  | TypeConst Dom.TBool
    | TypeConst Dom.TInt as ty -> Some ty
  | _ -> None

let type_usub = function
  | TypeConst Dom.TInt
    | TypeConst Dom.TFloat
    | TypeConst Dom.TSpan
    | TypeConst (Dom.TMoney _) as ty -> Some ty
  | _ -> None

let type_badd = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt 
    | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    | TypeConst Dom.TFloat, TypeConst Dom.TInt
    | TypeConst Dom.TStr, TypeConst Dom.TStr
    | TypeConst Dom.TTime, TypeConst Dom.TSpan
    | TypeConst Dom.TSpan, TypeConst Dom.TSpan as args
    -> Some (fst args)
  | TypeConst (Dom.TMoney c), TypeConst (Dom.TMoney c')
       when String.equal c c'
    -> Some (TypeConst (Dom.TMoney c))
  | TypeConst Dom.TInt, TypeConst Dom.TFloat
    | TypeConst Dom.TSpan, TypeConst Dom.TTime as args
    -> Some (snd args)
  | _ -> None

let type_bsub = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt 
    | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    | TypeConst Dom.TFloat, TypeConst Dom.TInt
    | TypeConst Dom.TTime, TypeConst Dom.TSpan
    | TypeConst Dom.TSpan, TypeConst Dom.TSpan as args
    -> Some (fst args)
  | TypeConst (Dom.TMoney c), TypeConst (Dom.TMoney c')
       when String.equal c c'
    -> Some (TypeConst (Dom.TMoney c))
  | TypeConst Dom.TInt, TypeConst Dom.TFloat
    -> Some (TypeConst Dom.TFloat)
  | _ -> None

let type_bmul = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt
    | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    | TypeConst Dom.TInt, TypeConst Dom.TFloat
    | TypeConst Dom.TInt, TypeConst Dom.TSpan
    | TypeConst Dom.TFloat, TypeConst Dom.TSpan as args
    -> Some (snd args)
  | TypeConst Dom.TInt, TypeConst (Dom.TMoney c)
    | TypeConst Dom.TFloat, TypeConst (Dom.TMoney c)
    | TypeConst (Dom.TMoney c), TypeConst Dom.TInt
    | TypeConst (Dom.TMoney c), TypeConst Dom.TFloat
    -> Some (TypeConst (Dom.TMoney c))
  | TypeConst Dom.TFloat, TypeConst Dom.TInt
    | TypeConst Dom.TSpan, TypeConst Dom.TInt
    | TypeConst Dom.TSpan, TypeConst Dom.TFloat as args 
    -> Some (fst args)
  | _ -> None

let type_bdiv = function
  | TypeConst Dom.TInt, TypeConst Dom.TFloat as args
    -> Some (snd args)
  | TypeConst Dom.TInt, TypeConst Dom.TInt 
    | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    | TypeConst Dom.TFloat, TypeConst Dom.TInt
    | TypeConst Dom.TSpan, TypeConst Dom.TInt
    | TypeConst Dom.TSpan, TypeConst Dom.TFloat as args
    -> Some (fst args)
  | TypeConst (Dom.TMoney c), TypeConst Dom.TInt
    | TypeConst (Dom.TMoney c), TypeConst Dom.TFloat
    -> Some (TypeConst (Dom.TMoney c))
  | _ -> None

let type_bpow = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt
    -> Some (TypeConst Dom.TInt)
  | TypeConst Dom.TFloat, TypeConst Dom.TFloat
    -> Some (TypeConst Dom.TFloat)
  | _ -> None

let type_band = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt
    -> Some (TypeConst Dom.TInt)
  | TypeConst Dom.TBool, TypeConst Dom.TBool
    -> Some (TypeConst Dom.TBool)
  | _ -> None

let type_beq (ty, ty') =
  if TypeTerm.equal ty ty' then
    Some ty
  else
    None

let type_blt = function
  | TypeConst Dom.TInt, TypeConst Dom.TInt
  | TypeConst Dom.TFloat, TypeConst Dom.TFloat
  | TypeConst Dom.TInt, TypeConst Dom.TFloat
  | TypeConst Dom.TFloat, TypeConst Dom.TInt
  | TypeConst Dom.TTime, TypeConst Dom.TTime
  | TypeConst Dom.TSpan, TypeConst Dom.TSpan
    -> Some (TypeConst Dom.TBool)
  | TypeConst (Dom.TMoney c), TypeConst (Dom.TMoney c') when String.equal c c'
    -> Some (TypeConst Dom.TBool)
  | _ -> None

let rec type_term tevents tfunctions taliases typed_vars (v: Term.t) t_alias: ('typed_vars * TTerm.t) =
  match v.trm with
  | Var x ->
     begin match Map.find typed_vars x, t_alias with
     | Some a', _ -> (typed_vars, TTerm.make (TTerm.var x) { pos = v.info.pos; typ = a' })
     | None, Some typ -> (Map.add_exn typed_vars ~key:x ~data:typ, TTerm.make (TTerm.var x) { pos = v.info.pos; typ })
     | _, _ -> let err_msg = Printf.sprintf "Cannot infer the type of variable %s" x in
               Errors.type_error err_msg v.info.pos
     end
  | Const c -> (typed_vars, TTerm.make (TTerm.const c) { pos = v.info.pos; typ = TypeConst (Dom.tt_of_domain c) })
  | App (f_name, trms) ->
     begin
       let f (typed_vars, trms) trm (arg_name, arg_type) =
         let typed_vars, trm = type_term tevents tfunctions taliases typed_vars trm (Some arg_type) in
         if TypeTerm.equal trm.info.typ arg_type then
           (typed_vars, trm :: trms)
         else
           let err_msg =
             Printf.sprintf
               "Type mismatch for argument %s of function %s: expected '%s', found '%s'"
               arg_name f_name (TypeTerm.value_to_string trm.info.typ)
               (TypeTerm.value_to_string arg_type) in
           Errors.type_error err_msg v.info.pos
       in
       match Map.find tfunctions f_name with
       | Some (arg_types, typ, _) ->
          begin match List.fold2 trms arg_types ~init:(typed_vars, []) ~f with
          | Ok (typed_vars, trms) ->
            (typed_vars, TTerm.make (TTerm.app f_name (List.rev trms)) { pos = v.info.pos; typ })
          | Unequal_lengths ->
             let err_msg = Printf.sprintf "Function %s expects %d arguments, found %d"
                             f_name (List.length arg_types) (List.length trms) in
             Errors.type_error err_msg v.info.pos
          end
       | None ->
        let err_msg = Printf.sprintf "Function '%s' is undefined" f_name in
        Errors.type_error err_msg v.info.pos
     end
  | Unop (op, trm) ->
     begin
       let f_op = match op with
         | UNot -> type_unot
         | USub -> type_usub in
       let t_alias = Option.find_map t_alias ~f:f_op in
       let typed_vars, trm = type_term tevents tfunctions taliases typed_vars trm t_alias in
       match f_op trm.info.typ with
       | Some typ -> (typed_vars, TTerm.make (TTerm.unop UNot trm) { pos = v.info.pos; typ })
       | None ->
         let err_msg = Printf.sprintf "Unary (!) expects type TBool, found '%s'"
                         (TypeTerm.value_to_string trm.info.typ) in
         Errors.type_error err_msg v.info.pos
     end
  | Binop (trm, op, trm') ->
     begin
       let typed_vars, trm  = type_term tevents tfunctions taliases typed_vars trm None in
       let typed_vars, trm' = type_term tevents tfunctions taliases typed_vars trm' None in
       let f_op = match op with
         | BAdd -> type_badd
         | BSub -> type_bsub
         | BMul -> type_bmul
         | BDiv -> type_bdiv
         | BPow -> type_bpow
         | BAnd | BOr | BXor -> type_band
         | BEq | BNeq -> type_beq
         | BLt | BLeq | BGt | BGeq -> type_blt
       in
       match f_op (trm.info.typ, trm'.info.typ) with
       | Some typ -> (typed_vars, TTerm.make (TTerm.binop trm op trm') { pos = v.info.pos; typ })
       | None ->
          let err_msg = Printf.sprintf "The types '%s' and '%s' are not applicable to binary plus (+)"
                          (TypeTerm.value_to_string trm.info.typ)
                          (TypeTerm.value_to_string trm'.info.typ) in
          Errors.type_error err_msg v.info.pos
     end
  | Proj (trm, p) ->
     let check_sum typed_vars trm kvs =
       match List.find kvs ~f:(fun (k, _) -> String.equal k p) with
       | Some (_, typ) -> typed_vars, TTerm.make (TTerm.proj trm p) { typ; pos = v.info.pos } 
       | None -> let err_msg = 
                   Printf.sprintf "The type '%s' does not have a '%s' field"
                     (TypeTerm.value_to_string trm.info.typ) p in
                 Errors.type_error err_msg v.info.pos in
     let not_sum_type trm =
       let err_msg =
         Printf.sprintf "The type '%s' could not be recognized as a sum type, it does not have a '%s' field"
           (TypeTerm.value_to_string TTerm.(trm.info.typ)) p in
       Errors.type_error err_msg v.info.pos in
     let typed_vars, trm = type_term tevents tfunctions taliases typed_vars trm None in
     begin
       match TypeTerm.eval taliases trm.info.typ with
       | Some (TypeTerm.TypeSum kvs) -> check_sum typed_vars trm kvs
       | _ -> not_sum_type trm
     end
  | Record kvs ->
     let dups = List.find_all_dups (List.map kvs ~f:fst) ~compare:String.compare in
     if List.length dups > 0 then
       let err_msg =
         Printf.sprintf "The following fields are repeated in sum type: '%s'"
           (String.concat ~sep:", " dups) in
       Errors.type_error err_msg v.info.pos
     else
       let f typed_vars (k, v) =
         let typed_vars, trm = type_term tevents tfunctions taliases typed_vars v None in
         (typed_vars, (k, trm)) in
       let typed_vars, ktrms = List.fold_map kvs ~init:typed_vars ~f in
       let trm = TTerm.Record ktrms in
       let typ =
         TypeTerm.TypeSum (List.map ktrms ~f:(fun (k, v) -> (k, v.info.typ))) in
       typed_vars, { trm; info = { typ; pos = v.info.pos } }
       
let type_terms event_name trms t_vars pos tevents tfunctions taliases =
  let args = match Map.find tevents event_name with
    | Some (_, args, _, _) -> args
    | None -> let err_msg = Printf.sprintf
                              "Event '%s' is undefined"
                              event_name
              in Errors.type_error err_msg pos
  in
  let acc_function (t_vars, trms) (arg_name, type_alias) trm =
    let t_vars, trm = type_term tevents tfunctions taliases t_vars trm (Some type_alias) in
    let ty = TTerm.(trm.info.typ) in
    match TypeTerm.lub ty type_alias taliases with
    | Some typ -> let trm = { trm with info = { trm.info with typ } } in (t_vars, trm :: trms)
    | None ->
      let err_msg = Printf.sprintf "Type mismatch for argument %s of event %s: expected '%s', found '%s'"
                      arg_name event_name (TypeTerm.value_to_string type_alias)
                      (TypeTerm.value_to_string ty) in
      Errors.type_error err_msg pos
  in
  match List.fold2 args trms ~init:(t_vars, []) ~f:acc_function with
  | Ok (t_vars', trms') -> (t_vars', List.rev trms')
  | Unequal_lengths ->
     let err_msg = Printf.sprintf
                     "Number of arguments doesn't match for event '%s'"
                     event_name
     in
     Errors.type_error err_msg pos

let unpack_functional tevents trm' (trm: Term.t) = match trm.trm with
  | Term.App (f, trms) ->
     (match Map.find tevents f with
      | Some (Event (_, Functional) as et, _, _, _) ->
         Some (f, trms @ [trm'], et)
      | _ -> None)
  | _ -> None

let unpack_variable tevents trm' (trm: Term.t) = match trm.trm with
  | Term.Var x ->
     (match Map.find tevents x with
      | Some (Event (_, Variable) as et, _, _, _) ->
         Some (x, [trm'], et)
      | _ -> None)
  | _ -> None

let unpack_special_eq tevents trm trm' =
  List.find_map
    [unpack_functional tevents trm trm';
     unpack_functional tevents trm' trm;
     unpack_variable tevents trm trm';
     unpack_variable tevents trm' trm]
    ~f:(fun x -> x)

let rec type_formula (s: tprog) ?(event_type=Event (false, Standard)) t_vars (f: Formula.t): ('t_vars * Tformula.t) =
  let t_vars, form, event_type_opt = match f.form with
  | Formula.TT -> t_vars, Tformula.tt, None
  | FF -> t_vars, Tformula.ff, None
  | EqConst ({ trm = Binop (x, BEq, y); info }, Dom.Bool true) -> begin
    match unpack_special_eq s.tevents x y with
    | Some (event_name, trms, event_type) ->
       let t_vars, f = type_formula s ~event_type t_vars (Formula.make (Formula.predicate event_name trms) f.info) in
       t_vars, f.form, Some event_type
    | None -> begin
      let t_vars, x' = type_term s.tevents s.tfunctions s.taliases t_vars x None in
      let t_vars, y' = type_term s.tevents s.tfunctions s.taliases t_vars y (Some x'.info.typ) in
      if TypeTerm.equal x'.info.typ y'.info.typ then
        t_vars,
        EqConst ({ trm = TTerm.binop x' BEq y';
                   info = { pos = info.pos; typ = TypeTerm.TypeConst (Dom.TBool) } },
                 Dom.Bool true), None
      else
        let err_msg = Printf.sprintf "Ill-typed argument types in equality: '%s' vs '%s'"
                        (TypeTerm.to_string x'.info.typ) (TypeTerm.to_string y'.info.typ) in
        Errors.type_error err_msg f.info.pos
      end
    end
  | EqConst (t, c) ->
     let t_vars, t' = type_term s.tevents s.tfunctions s.taliases t_vars t None in
     begin match t'.info.typ with
       | TypeTerm.TypeConst Dom.TBool ->
          let c = TTerm.{ trm = TTerm.Const c;
                          info = { pos = t'.info.pos; typ = TypeTerm.TypeConst Dom.TBool } } in
          (t_vars,
           EqConst ({ trm = TTerm.binop t' BEq c;
                      info = { pos = f.info.pos; typ = TypeTerm.TypeConst (Dom.TBool) } },
                    Dom.Bool true), None)
       | _ -> let err_msg = Printf.sprintf "Ill-typed term type: '%s'" (TypeTerm.to_string t'.info.typ) in
              Errors.type_error err_msg f.info.pos
     end
  | Predicate (event_name, trms) ->
     let t_vars, trms = type_terms event_name trms t_vars f.info.pos s.tevents s.tfunctions s.taliases in
     t_vars, Tformula.predicate event_name trms, Some event_type
  | Agg (u, op, x, y, f) ->
     let t_vars, f = type_formula s t_vars f in
     let t_vars, x = type_term s.tevents s.tfunctions s.taliases t_vars x None in
     let t_vars = match x.info.typ with
       | TypeConst x_tt ->
          begin
            match Aggregation.ret_tt op x_tt with
            | None ->
               let err_msg =
                 Printf.sprintf "Aggregation operator '%s' and term type '%s' are incompatible"
                   (MFOTL_lib.Aggregation.op_to_string op) (Dom.tt_to_string x_tt) in
               Errors.type_error err_msg f.info.pos
            | Some u_tt -> Map.add_exn t_vars ~key:u ~data:(TypeTerm.TypeConst u_tt)
          end
       | _ ->
          let err_msg =
            Printf.sprintf "Aggregation is only possible on base types, not '%s'"
              (TypeTerm.to_string x.info.typ) in
          Errors.type_error err_msg f.info.pos
     in
     t_vars, Tformula.agg u op x y f, None
  | Neg f ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.neg f, None
  | And (side, fs) ->
     let t_vars, fs = List.fold_map fs ~init:t_vars ~f:(type_formula s) in
     t_vars, Tformula.conjs side fs, None
  | Or (side, fs) ->
     let t_vars, fs = List.fold_map fs ~init:t_vars ~f:(type_formula s) in
     t_vars, Tformula.disjs side fs, None
  | Imp (side, f, g) ->
     let t_vars, f = type_formula s t_vars f in
     let t_vars, g = type_formula s t_vars g in
     t_vars, Tformula.imp side f g, None
  | Exists (x, f) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.exists x f, None
  | Forall (x, f) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.forall x f, None
  | Prev (i, f) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.prev i f, None
  | Next (i, f) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.next i f, None
  | Once (i, f) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.once i f, None
  | Eventually (i, f) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.eventually i f, None 
  | Historically (i, f) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.historically i f, None
  | Always (i, f) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.always i f, None
  | Since (side, i, f, g) ->
     let t_vars, f = type_formula s t_vars f in
     let t_vars, g = type_formula s t_vars g in
     t_vars, Tformula.since side i f g, None
  | Until (side, i, f, g) ->
     let t_vars, f = type_formula s t_vars f in
     let t_vars, g = type_formula s t_vars g in
     t_vars, Tformula.until side i f g, None
  | Type (f, ty) ->
     let t_vars, f = type_formula s t_vars f in
     t_vars, Tformula.ftype f ty, None
  | Predicate' _ | Let _ | Let' _  | Top _ ->
     raise (Invalid_argument (Printf.sprintf "typing not implemented for %s" (Formula.to_string f)))
  in
  let type_variable_instantiation t_vars (k, v) =
    let t_vars, v = type_term s.tevents s.tfunctions s.taliases t_vars v None in
    t_vars, (k, v) in
  let t_vars, variable_instantiations =
    List.fold_map ~init:t_vars ~f:type_variable_instantiation f.info.variable_instantiations in
  t_vars, { form; info = Tformula.{ variable_instantiations; pos = f.info.pos; event_type_opt} }

let type_patt s t_vars (pf: Lex.Pattern.patt) : ('t_vars * Pattern.patt) = match pf with
  | PPresent -> t_vars, Pattern.PPresent
  | PEventually i -> t_vars, PEventually i
  | PAlways i -> t_vars, PAlways i
  | PUntil (i, f) -> let t_vars, f = type_formula s t_vars f in t_vars, PUntil (i, f)
  | POnce i -> t_vars, POnce i
  | PHistorically i -> t_vars, PHistorically i
  | PSince (i, f) -> let t_vars, f = type_formula s t_vars f in t_vars, PSince (i, f)

let type_formulas s t_vars (fs: Formula.t list): ('t_vars * Tformula.t list) =
  List.fold_map fs ~init:t_vars ~f:(type_formula s)

let type_pformula tprog t_vars (pf: Lex.Pattern.t): ('free_vars * 't_vars * Pattern.t) = 
  let t_vars, fs = type_formulas tprog t_vars pf.fs in  let t_vars, patt = type_patt tprog t_vars pf.patt in
  let tpf = Pattern.make patt fs in
  let vars = Pattern.fv tpf in
  vars, t_vars, tpf

let type_rule s pos = function
  | SRule (_, rule_id, type_fixes, rule, doc_string) -> begin
      let label' = Label.set_rule_id_force rule_id s.label  in
      let _ = Label.valid_rule_label pos label' in
      let t_vars = Map.of_alist_exn (module String) type_fixes in
      let rule_num = fresh () in
      let section_kinds_are_in_order (k1, s1) (k2, s2) = match compare_section_kind k1 k2 with
        | i when i = 0 -> 
          let err_msg = Printf.sprintf "Section kind %s is defined more than once: '%s' and '%s'" (string_of_section_kind k1) s1 s2 in
          Errors.reference_error err_msg pos
        | i when i < 0 -> 
          let err_msg = Printf.sprintf "Section kinds inside reference must be strictly 'decreasing', but '%s \"%s\"' is followed by '%s \"%s\"' which is at a greater level" 
            (string_of_section_kind k1) s1 (string_of_section_kind k2) s2
          in
          Errors.reference_error err_msg pos
        | _ -> (k2, s2)
      in
      let decreasing_section_kinds (r: Lex.Ref.t) = match r with
        | {sks=[]; rule=None; _} -> Errors.reference_error "references must contain at least one reference" r.pos
        | {sks=r::rs; _} -> List.fold ~init:r ~f:section_kinds_are_in_order rs |> ignore
        | {sks=[]; rule=Some _; _} -> ()
      in
      let s, t_vars, rule = 
        let merge_reference_with_label (l: Label.t) (ref_expr: Lex.Ref.t) =
          begin match Label.highest_level l with
          | (Label.LSection (Article 0, _)) ->
             let init = Label.qualified_label l in
             let rule_id = ref_expr.rule in
             let aux acc (level, name) = Label.set pos level (name, None) acc in
             let label = Label.set_rule_id rule_id (List.fold ~init:init ~f:aux ref_expr.sks) in
             Ref.from_lex_ref ref_expr label
          | _ ->
             let rule_id = ref_expr.rule in
             let aux acc (level, name) = Label.set pos level (name, None) acc in
             let label = Label.set_rule_id rule_id (List.fold ~init:l ~f:aux ref_expr.sks) in
             Ref.from_lex_ref ref_expr label
          end in
        let var_term_of_ident_and_positions t_vars x =
          TTerm.{ trm = TTerm.var x; info = { pos = LexingInfo.dummy; typ = Map.find_exn t_vars x } } in
        let arg_of_ident_and_positions t_vars x = (x, Map.find_exn t_vars x) in
        let rec process_rule s t_vars = function
          | Exception (pos, pf, refs) ->
             let _ = List.map ~f:decreasing_section_kinds refs in
             debug (String.concat ~sep:"\n" (List.map refs ~f:Lex.Ref.to_string));
            let reference_labels = List.map ~f:(merge_reference_with_label s.label) refs in
            debug (String.concat ~sep:"\n" (List.map reference_labels ~f:(fun r -> Label.string_of_label r.label)));
            let p_name = "Exception" ^ string_of_int rule_num in (* TODO: mark 'Exception' as an internal name and prevent user-defined events to start with that *)
            let vars, t_vars, tpf = type_pformula s.tprog t_vars pf in
            let terms = List.map (Set.elements vars) ~f:(var_term_of_ident_and_positions t_vars) in
            let args = List.map (Set.elements vars) ~f:(arg_of_ident_and_positions t_vars) in
            let pred = Tformula.make (Tformula.predicate p_name terms)
                         { Tformula.Info.dummy with event_type_opt = Some (Event (false, Standard)) } in
            let s' = add_exception_first_pass rule_num pred reference_labels s in
            let s' = add_tevent Lex.Exception p_name args Enftype.itl None s' LexingInfo.dummy in 
            s', t_vars, TException (pos, tpf, reference_labels, pred)
          | Scope (pos, pf, refs) ->
            let _ = List.map ~f:decreasing_section_kinds refs in
            let reference_labels = List.map ~f:(fun tref -> merge_reference_with_label s.label tref) refs in
            let p_name = "Scope" ^ string_of_int rule_num in (* TODO: mark 'Scope' as an internal name and prevent user-defined events to start with that *)
            let vars, t_vars, tpf = type_pformula s.tprog t_vars pf in
            let terms = List.map (Set.elements vars) ~f:(var_term_of_ident_and_positions t_vars) in
            let args = List.map (Set.elements vars) ~f:(arg_of_ident_and_positions t_vars) in
            let pred = Tformula.make (Tformula.predicate p_name terms)
                         { Tformula.Info.dummy with event_type_opt = Some (Event (false, Standard)) } in
            let s' = add_scope_first_pass rule_num pred reference_labels s in
            let s' = add_tevent Lex.Exception p_name args Enftype.itl None s' LexingInfo.dummy in 
            s', t_vars, TScope (pos, tpf, reference_labels, pred)
          | Obligation (pos, pf1, pf2, rt, rcs) ->
            let _, t_vars, tpf1 = type_pformula s.tprog t_vars pf1 in
            let _, t_vars, tpf2 = type_pformula s.tprog t_vars pf2 in
            s, t_vars, TObligation (pos, tpf1, tpf2, rt, rcs)
          | Permission (pos, pf1, pf2, rt, rcs) ->
            let _, t_vars, tpf1 = type_pformula s.tprog t_vars pf1 in
            let _, t_vars, tpf2 = type_pformula s.tprog t_vars pf2 in
            s, t_vars, TPermission (pos, tpf1, tpf2, rt, rcs)
          | Constitutive (pos, pf1, f2) ->
            let _, t_vars, tpf1 = type_pformula s.tprog t_vars pf1 in
            let t_vars, tf2 = type_formulas s.tprog t_vars f2 in
             s, t_vars, TConstitutive (pos, tpf1, tf2)
          | ExceptionC (pos, pf1, refs, f2) ->
             let s, t_vars, tf = process_rule s t_vars (Exception (pos, pf1, refs)) in
             let s, t_vars, tg = process_rule s t_vars (Constitutive (pos, pf1, f2)) in
             match tf, tg with
             | TException (pos, tpf1, reference_labels, pref), TConstitutive (_, _, tf2)
               -> s, t_vars, TExceptionC (pos, tpf1, reference_labels, pref, tf2)
             | _, _ -> assert false
        in process_rule s t_vars rule
      in
      let s' = add_vars rule_num t_vars s in
      let s'' = add_rule pos rule_num label' s' in
      let doc_string' = Option.map doc_string ~f:(fun x -> TALex x) in
      add_tstmt (TSRule (pos, rule_num, label', type_fixes, rule, doc_string')) s''
    end
  | _ -> assert false

let type_stmt s = function
  | SImport (pos, import_format, idents) ->
     add_tstmt (TSImport (pos, idents, import_format)) s
  | SSection (pos, section_kind, label_description, title) ->
     let s = set_labels pos section_kind (label_description, title) s in
     let title' = Option.map title ~f:(fun x -> TALex x) in
     let s' = add_section pos s.label s in
     add_tstmt (TSSection (section_kind, s.label, label_description, title')) s'
  | SRule (pos, _, _, _, _) as rule -> type_rule s pos rule
  | SEvent (pos, event_type, name, args, pol, ds) ->
     add_tevent event_type name args pol ds s pos
  | SType (pos, name, typ, doc_string) ->
     add_talias name typ doc_string s pos
  | SFunction (pos, name, arg_types, return_type, doc_string) ->
     add_tfunction name arg_types return_type doc_string s pos
  | SNote (_, text) -> add_tstmt (TSNote text) s

(* Checking of variable types *)
    
let merge_type_maps pos m1 m2 label = Map.merge m1 m2 ~f:(fun ~key:k -> function
  | `Both (a1, a2) when TypeTerm.equal a1 a2 -> Some a1
  | `Both (a1, a2) -> let err_msg = Printf.sprintf
        "Variable '%s' has type '%s' in rule '%s', but was expected to have type '%s'"
        k (TypeTerm.value_to_string a2) label (TypeTerm.value_to_string a1)
      in Errors.type_error err_msg pos
  | `Left t
  | `Right t -> Some t)

let check_var_types tprog =
  let var_equivalence_classes = Label.RuleTree.rules_with_shared_variable_scopes tprog.rule_tree in
  let f0 acc' key =
    let var_types = Map.find_exn tprog.variables key in
    let label = Label.RuleTree.string_of_rule_idx tprog.rule_tree key in
    let pos = Label.RuleTree.pos_of_rule_idx tprog.rule_tree key in
    merge_type_maps pos var_types acc' label
  in
  let f1 keys = (keys, Set.fold keys ~init:(Map.empty (module String)) ~f:f0) in
  let updated_vars = List.map var_equivalence_classes ~f:f1 in
  let f2 v acc key = Map.update acc key ~f:(fun _ -> v) in
  let f3 m (keys, v) = Set.fold keys ~init:m ~f:(f2 v) in
  let vars = List.fold ~init:(Map.empty (module Int)) ~f:f3 updated_vars in
  vars

(* Main typing function *)

let do_type tprog prog =
  let init = { empty with tprog } in
  (* First pass: type statements *)
  let s = List.fold prog.stmts ~init ~f:type_stmt in
  (* Second pass: exceptions *)
  let tprog' = List.fold s.exceptions_first_pass ~init:s.tprog
                 ~f:(fun acc (i,f,refs) -> Tlex.add_exception i f refs acc) in
  let tprog'' = List.fold s.scopes_first_pass ~init:tprog'
                  ~f:(fun acc (i,f,refs) -> Tlex.add_scope i f refs acc) in
  let vars = check_var_types tprog'' in
  {
    tstmts = List.rev tprog''.tstmts;
    taliases = tprog''.taliases;
    tevents = tprog''.tevents;
    tfunctions = tprog''.tfunctions;
    variables = vars;
    rule_tree = tprog''.rule_tree;
    exception_predicates = tprog''.exception_predicates;
    scope_predicates = tprog''.scope_predicates
  }
