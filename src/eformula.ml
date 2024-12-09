(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Core

module Modules = MFOTL_lib.Modules
module Enftype = MFOTL_lib.Enftype
module Side = MFOTL_lib.Side

module StringVar = Term.StringVar

let debug_eformula = ref true
let debug msg = if !debug_eformula then Errors.debug_print ~f_name:(Some "eformula.ml") msg else ignore msg

type einfo_type = {
    enftype: Enftype.t;
    variable_instantiations: (string * TTerm.t) list;
    id: int;
    pos: LexingInfo.t;
    event_type_opt: Lex.event_type option;
    flag_opt: bool option;
  } [@@deriving compare, sexp_of, hash, equal]

module Info : Modules.I with type t = einfo_type = struct
  
  type t = einfo_type [@@deriving compare, sexp_of, hash, equal]

  let rec string_of_instantiations = function
    | [] -> ""
    | [(x, t)] -> Printf.sprintf "%s <- %s" x (TTerm.value_to_string t)
    | (x, t) :: insts ->  Printf.sprintf "%s <- %s; %s" x (TTerm.value_to_string t) (string_of_instantiations insts)

  let to_string _ s info =
    match info.variable_instantiations with
    | [] -> s
    | _ -> Printf.sprintf "(%s; %s)" s (string_of_instantiations info.variable_instantiations)
  
  let dummy = {
      enftype = Enftype.bot;
      variable_instantiations = [];
      id = -1;
      pos = LexingInfo.dummy;
      event_type_opt = None;
      flag_opt = None;
    }

end

module ETerm = TTerm

include MFOTL_lib.MFOTL.Make(Info)(StringVar)(Dom)(ETerm)

let rec max_id_core (f : t) = match f.form with
  | TT
    | FF
    | EqConst _
    | Predicate _ -> 0
  | Predicate' (_, _, f)
    | Let (_, _, _, _, f)
    | Let' (_, _, _, f)
    | Agg (_, _, _, _, f)
    | Top (_, _, _, _, f)
    | Neg f
    | Exists (_, f)
    | Forall (_, f)
    | Prev (_, f)
    | Next (_, f)
    | Once (_, f)
    | Eventually (_, f)
    | Historically (_, f)
    | Always (_, f)
    | Type (f, _)
    -> max_id f
  | And (_, fs)
    | Or (_, fs)
    -> Option.value ~default:0 (
           List.max_elt (List.map fs ~f:max_id) ~compare:Int.compare)
  | Imp (_, f1, f2)
    | Since (_, _, f1, f2)
    | Until (_, _, f1, f2) 
    -> Int.max (max_id f1) (max_id f2)

and max_id f = Int.max f.info.id (max_id_core f)

let dummy = LexingInfo.dummy
let (+.+) (f:t) (g:t) = LexingInfo.(f.info.pos ++ g.info.pos)

let tbigcauconj = function
  | [] -> make tt { Info.dummy with enftype = Enftype.cau }
  | h::t -> List.fold t ~init:h
              ~f:(fun f g -> make (conj LR f g)
                               { Info.dummy with enftype = Enftype.cau; pos = f +.+ g })

let tbigsupconj idx = function
  | [] -> make_dummy tt
  | h::t ->
    let aux i f g =
      if i < idx then
        make (conj R f g) { Info.dummy with enftype = Enftype.sup; pos = f +.+ g }
      else
        make (conj L f g) { Info.dummy with enftype = Enftype.sup; pos = f +.+ g }
    in
    List.foldi t ~init:h ~f:aux

let tbignonconj = function
  | [] -> make_dummy tt
  | h::t -> List.fold t ~init:h
              ~f:(fun f g -> make (conj N f g)
                               { Info.dummy with enftype = Enftype.bot; pos = f +.+ g })

let tbigcaudisj idx = function
  | [] -> make_dummy tt
  | h::t ->
    let aux i f g =
      if i < idx then
        make (disj R f g) { Info.dummy with pos = f +.+ g }
      else
        make (disj L f g) { Info.dummy with pos = f +.+ g }
    in
    List.foldi t ~init:h ~f:aux

let tbigsupdisj = function
  | [] -> make tt { Info.dummy with enftype = Enftype.sup }
  | h::t -> List.fold t ~init:h
              ~f:(fun f g -> make (disj LR f g)
                               { Info.dummy with enftype = Enftype.sup; pos = f +.+ g })

let tbignondisj = function
  | [] -> make_dummy tt
  | h::t -> List.fold t ~init:h
              ~f:(fun f g -> make (disj N f g) { Info.dummy with pos = f +.+ g })

let tbigcauforall vars f =
  List.fold_right vars ~init:f
    ~f:(fun x f -> make (forall x f) { Info.dummy with enftype = Enftype.cau;
                                                           pos = f.info.pos })

let tbigcauexists vars f =
  List.fold_right vars ~init:f
    ~f:(fun x f -> make (exists x f) { Info.dummy with enftype = Enftype.cau;
                                                           pos = f.info.pos })

let rec core_of_tformula ?id:(id=1) d = 
  let lof_formula = of_tformula ~id:(d*id)
  and rof_formula = of_tformula ~id:(d*id+1)
  and iof_formula i = of_tformula ~id:(d*id+i) in
  function
  | Tformula.TT -> TT, None
  | FF -> FF, None
  | EqConst (x, y) -> 
     (if Dom.equal y (Dom.Bool true) then
       EqConst (x, Dom.Bool true)
     else
       EqConst (ETerm.make
                  (ETerm.Binop (x, Term.Bop.BEq, ETerm.make_dummy (ETerm.const y)))
                  { pos = x.info.pos; typ = TypeTerm.TypeConst (Dom.TBool)}, Dom.Bool true)), None
  | Predicate (e, t) -> Predicate (e, t), None
  | Predicate' (s, trms, f) -> Predicate' (s, trms, lof_formula f), None
  | Let (s, ty_opt, vars, f, g) -> Let (s, ty_opt, vars, lof_formula f, rof_formula g), None
  | Let' (s, vars, f, g) -> Let' (s, vars, lof_formula f, rof_formula g), None
  | Agg (s, op, x, y, f) -> Agg (s, op, x, y, lof_formula f), None
  | Top (s, op, x, y, f) -> Top (s, op, x, y, lof_formula f), None
  | Neg f -> Neg (lof_formula f), None
  | And (s, fs) -> And (s, List.mapi ~f:iof_formula fs), None
  | Or (s, fs) -> Or (s, List.mapi ~f:iof_formula fs), None
  | Imp (s, f, g) -> Imp (s, lof_formula f, rof_formula g), None
  | Exists (x, f) -> Exists (x, lof_formula f), None
  | Forall (x, f) -> Forall (x, lof_formula f), None
  | Prev (i, f) -> Prev (i, lof_formula f), None
  | Next (i, f) -> Next (i, lof_formula f), None
  | Once (i, f) -> Once (i, lof_formula f), None
  | Eventually (i, f) -> Eventually (i, lof_formula f), Some true
  | Historically (i, f) -> Historically (i, lof_formula f), None 
  | Always (i, f) -> Always (i, lof_formula f), Some true
  | Since (s, i, f, g) -> Since (s, i, lof_formula f, rof_formula g), None
  | Until (s, i, f, g) -> Until (s, i, lof_formula f, rof_formula g), Some true
  | Type (f, ty) -> Type (lof_formula f, ty), None

and of_tformula ?id:(id=1) (f: Tformula.t) : t =
  let d = Tformula.deg f in
  let form, flag_opt = core_of_tformula ~id d f.form in
  { form; info = { variable_instantiations = f.info.variable_instantiations;
                   enftype = Enftype.obs;
                   event_type_opt = f.info.event_type_opt;
                   pos = f.info.pos; id; flag_opt; } }

let rec core_of_typed_tformula ?id:(id=1) d = 
  let lof_formula = of_typed_tformula ~id:(d*id)
  and rof_formula = of_typed_tformula ~id:(d*id+1)
  and iof_formula i = of_typed_tformula ~id:(d*id+i) in
  function
  | Tformula.TT -> TT, None
  | FF -> FF, None
  | EqConst (x, y) -> 
     (if Dom.equal y (Dom.Bool true) then
       EqConst (x, Dom.Bool true)
     else
       EqConst (ETerm.make
                  (ETerm.Binop (x, Term.Bop.BEq, ETerm.make_dummy (ETerm.const y)))
                  { pos = x.info.pos; typ = TypeTerm.TypeConst (Dom.TBool)}, Dom.Bool true)), None
  | Predicate (e, t) -> Predicate (e, t), None
  | Predicate' (s, trms, f) -> Predicate' (s, trms, lof_formula f), None
  | Let (s, ty_opt, vars, f, g) -> Let (s, ty_opt, vars, lof_formula f, rof_formula g), None
  | Let' (s, vars, f, g) -> Let' (s, vars, lof_formula f, rof_formula g), None
  | Agg (s, op, x, y, f) -> Agg (s, op, x, y, lof_formula f), None
  | Top (s, op, x, y, f) -> Top (s, op, x, y, lof_formula f), None
  | Neg f -> Neg (lof_formula f), None
  | And (s, fs) -> And (s, List.mapi ~f:iof_formula fs), None
  | Or (s, fs) -> Or (s, List.mapi ~f:iof_formula fs), None
  | Imp (s, f, g) -> Imp (s, lof_formula f, rof_formula g), None
  | Exists (x, f) -> Exists (x, lof_formula f), None
  | Forall (x, f) -> Forall (x, lof_formula f), None
  | Prev (i, f) -> Prev (i, lof_formula f), None
  | Next (i, f) -> Next (i, lof_formula f), None
  | Once (i, f) -> Once (i, lof_formula f), None
  | Eventually (i, f) -> Eventually (i, lof_formula f), Some true
  | Historically (i, f) -> Historically (i, lof_formula f), None 
  | Always (i, f) -> Always (i, lof_formula f), Some true
  | Since (s, i, f, g) -> Since (s, i, lof_formula f, rof_formula g), None
  | Until (s, i, f, g) -> Until (s, i, lof_formula f, rof_formula g), Some true
  | Type (f, ty) -> Type (lof_formula f, ty), None

and of_typed_tformula ?id:(id=1) (f: Tformula.typed_t) : t =
  let d = Tformula.deg f in
  let form, flag_opt = core_of_typed_tformula ~id d f.form in
  { form; info = { variable_instantiations = f.info.info.variable_instantiations;
                   enftype = f.info.enftype;
                   event_type_opt = f.info.info.event_type_opt;
                   pos = f.info.info.pos; id; flag_opt; } }

let of_tformulas = List.map ~f:of_tformula

let fix_side s f g =
  let open MFOTL_Enforceability(Tlex.Sig) in
  match s with
  | Side.LR -> if rank f < rank g then Side.L
               else Side.R
  | _ -> s

let rec to_formula (f: t): Formula.t =
  let variable_instantiations = List.map f.info.variable_instantiations ~f:(fun (x, t) -> (x, ETerm.to_term t)) in
  Formula.make (to_formula_core f.form) { variable_instantiations; pos = f.info.pos }

and to_formula_core: core_t -> Formula.core_t = function
  | TT -> TT
  | FF -> FF
  | EqConst (trm, c) -> EqConst (ETerm.to_term trm, c)
  | Predicate (e, trms) -> Predicate (e, List.map trms ~f:ETerm.to_term)
  | Predicate' (e, trms, f) -> Predicate' (e, List.map trms ~f:ETerm.to_term, to_formula f)
  | Let (s, ty_opt, vars, f, g) -> Let (s, ty_opt, vars, to_formula f, to_formula g)
  | Let' (s, vars, f, g) -> Let' (s, vars, to_formula f, to_formula g)
  | Agg (s, op, x, y, f) -> Agg (s, op, ETerm.to_term x, y, to_formula f)
  | Top (s, op, x, y, f) -> Top (s, op, List.map ~f:ETerm.to_term x, y, to_formula f)
  | Neg f -> Neg (to_formula f)
  | And (s, fs) -> And (fix_side s (List.hd_exn fs) (List.last_exn fs), List.map fs ~f:to_formula)
  | Or (s, fs) -> Or (fix_side s (List.hd_exn fs) (List.last_exn fs), List.map fs ~f:to_formula)
  | Imp (s, f, g) -> Imp (fix_side s f g, to_formula f, to_formula g)
  | Exists (x, f) -> Exists (x, to_formula f)
  | Forall (x, f) -> Forall (x, to_formula f)
  | Prev (i, f) -> Prev (i, to_formula f)
  | Next (i, f) -> Next (i, to_formula f)
  | Once (i, f) -> Once (i, to_formula f)
  | Eventually (i, f) -> Eventually (i, to_formula f)
  | Historically (i, f) -> Historically (i, to_formula f)
  | Always (i, f) -> Always (i, to_formula f)
  | Since (s, i, f, g) -> Since (fix_side s f g, i, to_formula f, to_formula g)
  | Until (s, i, f, g) -> Until (s, i, to_formula f, to_formula g)
  | Type (f, ty) -> Type (to_formula f, ty)

