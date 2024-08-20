(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Core
open Formula

module ETerm = Tformula.TTerm

type core_t =
  | ETT
  | EFF
  | EEqConst of ETerm.t * (Dom.t * Lexing.position list)
  | EPredicate of string * ETerm.t list * Lex.event_type
  | EAgg of string * Aggregation.op * ETerm.t * string list * t
  | ENeg of t
  | EAnd of Side.t * (t list)
  | EOr of Side.t * (t list)
  | EImp of Side.t * t * t
  | EIff of Side.t * Side.t * t * t
  | EExists of string * t
  | EForall of string * t
  | EPrev of Interval.t * t
  | ENext of Interval.t * t
  | EOnce of Interval.t * t
  | EEventually of Interval.t * bool * t
  | EHistorically of Interval.t * t
  | EAlways of Interval.t * bool * t
  | ESince of Side.t * Interval.t * t * t
  | EUntil of Side.t * Interval.t * bool * t * t
  | EType of t * ty

and t = { f: core_t; enftype: EnfType.t;
          id: int;
          positions: Lexing.position list }

let rec max_id_core = function
  | ETT
    | EFF
    | EEqConst _
    | EPredicate _ -> 0
  | EAgg (_, _, _, _, f)
    | ENeg f
    | EExists (_, f)
    | EForall (_, f)
    | EPrev (_, f)
    | ENext (_, f)
    | EOnce (_, f)
    | EEventually (_, _, f)
    | EHistorically (_, f)
    | EAlways (_, _, f)
    | EType (f, _)
    -> max_id f
  | EAnd (_, fs)
    | EOr (_, fs)
    -> Option.value ~default:0 (
           List.max_elt (List.map fs ~f:max_id) ~compare:Int.compare)
  | EImp (_, f1, f2)
    | EIff (_, _, f1, f2)
    | ESince (_, _, f1, f2)
    | EUntil (_, _, _, f1, f2) 
    -> Int.max (max_id f1) (max_id f2)

and max_id f = Int.max f.id (max_id_core f.f)

let make f enftype id positions = { f; enftype; id; positions }

let ett = ETT
let eff = EFF
let eeqconst x d = EEqConst (x, d)
let epredicate p_name trms event_type = EPredicate (p_name, trms, event_type)
let eneg f = ENeg f
let econj s f g = EAnd (s, [f; g])
let edisj s f g = EOr (s, [f; g])
let eimp s f g = EImp (s, f, g)
let eiff s t f g = EIff (s, t, f, g)
let eexists x f = EExists (x, f)
let eforall x f = EForall (x, f)
let eprev i f = EPrev (i, f)
let enext i f = ENext (i, f)
let eonce i f = EOnce (i, f)
let eeventually i f = EEventually (i, true, f)
let ehistorically i f = EHistorically (i, f)
let ealways i f = EAlways (i, true, f)
let esince s i f g = ESince (s, i, f, g)
let euntil s i f g = EUntil (s, i, true, f, g)
let etype s t = EType (s, t)

let tbigcauconj = function
  | [] -> make ett Non 0 []
  | h::t -> List.fold t ~init:h ~f:(fun f g -> make (econj LR f g) Cau 0 f.positions)

let tbigsupconj idx = function
  | [] -> make ett Non 0 []
  | h::t ->
    let aux i f g =
      if i < idx then make (econj R f g) Non 0 f.positions
      else            make (econj L f g) Non 0 f.positions
    in
    List.foldi t ~init:h ~f:aux

let tbignonconj = function
  | [] -> make ett Non 0 []
  | h::t -> List.fold t ~init:h ~f:(fun f g -> make (econj N f g) Non 0 f.positions)

let tbigcaudisj idx = function
  | [] -> make ett Non 0 []
  | h::t ->
    let aux i f g =
      if i < idx then make (edisj R f g) Non 0 f.positions
      else            make (edisj L f g) Non 0 f.positions
    in
    List.foldi t ~init:h ~f:aux

let tbigsupdisj = function
  | [] -> make ett Non 0 []
  | h::t -> List.fold t ~init:h ~f:(fun f g -> make (edisj LR f g) Sup 0 f.positions)

let tbignondisj = function
  | [] -> make ett Non 0 []
  | h::t -> List.fold t ~init:h ~f:(fun f g -> make (edisj N f g) Non 0 f.positions)

let tbigcauforall vars f =
  List.fold_right vars ~init:f ~f:(fun x f -> make (eforall x f) Non 0 f.positions)

let tbigcauexists vars f =
  List.fold_right vars ~init:f ~f:(fun x f -> make (eexists x f) Non 0 f.positions)

let rec core_of_tformula tevents ?id:(id=1) d = 
  let lof_formula = of_tformula tevents ~id:(d*id)
  and rof_formula = of_tformula tevents ~id:(d*id+1)
  and iof_formula i = of_tformula tevents ~id:(d*id+i) in
  function
  | Tformula.TTT -> ETT
  | TFF -> EFF
  | TEqConst (x, y) -> 
     (if ETerm.equal_core y.trm (ETerm.TConst (Dom.Bool true)) then
       EEqConst (x, (Dom.Bool true, y.positions))
     else
       EEqConst ({ trm = ETerm.TBinop (x, Formula.Term.BEq, y);
                   tt = TypeTerm.TypeConst (Dom.TBool);
                   positions = [] },
                 (Dom.Bool true, y.positions)))
  | TPredicate (e, t, et) -> EPredicate (e, t, et)
  | TAgg (s, op, x, y, f) -> EAgg (s, op, x, y, rof_formula f)
  | TNeg f -> ENeg (lof_formula f)
  | TAnd (s, fs) -> EAnd (s, List.mapi ~f:iof_formula fs)
  | TOr (s, fs) -> EOr (s, List.mapi ~f:iof_formula fs)
  | TImp (s, f, g) -> EImp (s, lof_formula f, rof_formula g)
  | TIff (s, t, f, g) -> EIff (s, t, lof_formula f, rof_formula g)
  | TExists (x, f) -> EExists (x, lof_formula f)
  | TForall (x, f) -> EForall (x, lof_formula f)
  | TPrev (i, f) -> EPrev (i, lof_formula f)
  | TNext (i, f) -> ENext (i, lof_formula f)
  | TOnce (i, f) -> EOnce (i, lof_formula f)
  | TEventually (i, f) -> EEventually (i, true, lof_formula f)
  | THistorically (i, f) -> EHistorically (i, lof_formula f)
  | TAlways (i, f) -> EAlways (i, true, lof_formula f)
  | TSince (s, i, f, g) -> ESince (s, i, lof_formula f, rof_formula g)
  | TUntil (s, i, f, g) -> EUntil (s, i, true, lof_formula f, rof_formula g)
  | TType (f, ty) -> EType (lof_formula f, ty)

and of_tformula tevents ?id:(id=1) (f: Tformula.t) : t =
  let d = Tformula.deg f in
  { f = core_of_tformula tevents ~id d f.f;
    enftype = EnfType.Obs;
    id;
    positions = f.positions }

let of_tformulas tevents = List.map ~f:(of_tformula tevents)

let rec fv ?(map=Map.empty (module String)) f =
  let aux0 v map p = Map.add_multi map ~key:v ~data:p in
  let aux1 map (v, ps) = List.fold ps ~init:map ~f:(aux0 v) in
  let merge_fun ~key:_ = function
    | `Left x | `Right x -> Some x
    | `Both (x, y) -> Some (x @ y)
  in
  let merge map1 map2 = Map.merge map1 map2  ~f:merge_fun in
  match f.f with
  | ETT | EFF -> map
  | EEqConst (x, _) ->
    ETerm.fv_list [x] |> List.fold ~init:map ~f:aux1
  | EPredicate (_, trms, _) ->
    ETerm.fv_list trms |> List.fold ~init:map ~f:aux1
  | EAgg (s, _, _, ys, _) ->
    ((s, f.positions) :: List.map ys ~f:(fun y -> (y, f.positions)))
    |> List.fold ~init:map ~f:aux1
  | EExists (x, g)
    | EForall (x, g) ->
      Map.filter_keys (fv g) ~f:(fun y -> not (String.equal x y))
      |> merge map (* merge with original map - doing it this way, instead of passing the map as an argument to fv above, we can avoid filtering out variables that are bound inside the quantifier, but free outside of it *)
  | ENeg f
    | EPrev (_, f)
    | EOnce (_, f)
    | EHistorically (_, f) 
    | EEventually (_, _, f)
    | EAlways (_, _, f)
    | ENext (_, f)
    | EType (f, _) -> fv ~map f
    | EImp (_, f1, f2)
    | EIff (_, _, f1, f2)
    | ESince (_, _, f1, f2)
    | EUntil (_, _, _, f1, f2) -> fv ~map:(fv ~map f2) f1
  | EAnd (_, fs)
    | EOr (_, fs) ->
      List.fold_left fs ~init:map ~f:(fun map f -> fv ~map f)

let rec rank = function
  | ETT | EFF -> 0
  | EEqConst _ -> 0
  | EPredicate (_, args, _) -> List.length args
  | EAgg (_, _, _, _, f) -> rank f.f
  | ENeg f
    | EExists (_, f)
    | EForall (_, f)
    | EPrev (_, f)
    | ENext (_, f)
    | EOnce (_, f)
    | EEventually (_, _, f)
    | EHistorically (_, f)
    | EAlways (_, _, f)
    | EType (f, _) -> rank f.f
    | EImp (_, f, g)
    | EIff (_, _, f, g)
    | ESince (_, _, f, g)
    | EUntil (_, _, _, f, g) -> rank f.f + rank g.f
  | EAnd (_, fs)
    | EOr (_, fs) -> List.fold_left (List.map fs ~f:(fun f -> rank f.f)) ~init:0 ~f:(+) 

let fix_side s f g =
  match s with
  | Side.LR -> if rank f < rank g then Side.L
               else Side.R
  | _ -> s

let rec to_formula (f: t): Formula.t = Formula.make_formula (to_formula_core f.f) f.positions

and to_formula_core: core_t -> Formula.core_t = function
  | ETT -> TT
  | EFF -> FF
  | EEqConst (trm, (c, c_pos)) ->
    Term (Formula.Term.binop trm.positions (ETerm.to_formula_term trm) Formula.Term.BEq (Formula.Term.const c_pos c))
  | EPredicate (e, trms, _) -> Predicate (e, List.map trms ~f:ETerm.to_formula_term)
  | EAgg (s, op, x, y, f) -> Agg (s, op, ETerm.to_formula_term x, y, to_formula f)
  | ENeg f -> Neg (to_formula f)
  | EAnd (s, fs) -> And (fix_side s (List.hd_exn fs).f (List.last_exn fs).f,
                         List.map fs ~f:to_formula)
  | EOr (s, fs) -> Or (fix_side s (List.hd_exn fs).f (List.last_exn fs).f,
                       List.map fs ~f:to_formula)
  | EImp (s, f, g) -> Imp (fix_side s f.f g.f, to_formula f, to_formula g)
  | EIff (s, t, f, g) -> Iff (fix_side s f.f g.f, fix_side t f.f g.f, to_formula f, to_formula g)
  | EExists (x, f) -> Exists (x, to_formula f)
  | EForall (x, f) -> Forall (x, to_formula f)
  | EPrev (i, f) -> Prev (i, to_formula f)
  | ENext (i, f) -> Next (i, to_formula f)
  | EOnce (i, f) -> Once (i, to_formula f)
  | EEventually (i, _, f) -> Eventually (i, to_formula f)
  | EHistorically (i, f) -> Historically (i, to_formula f)
  | EAlways (i, _, f) -> Always (i, to_formula f)
  | ESince (s, i, f, g) -> Since (fix_side s f.f g.f, i, to_formula f, to_formula g)
  | EUntil (s, i, _, f, g) -> Until (s, i, to_formula f, to_formula g)
  | EType (f, ty) -> Type (to_formula f, ty)

let rec op_to_string_core = function
  | ETT -> Printf.sprintf "⊤"
  | EFF -> Printf.sprintf "⊥"
  | EEqConst _ -> Printf.sprintf "="
  | EPredicate (r, trms, _) -> Printf.sprintf "%s(%s)" r (ETerm.list_to_string trms)
  | EAgg (_, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" (Aggregation.op_to_string op) (ETerm.value_to_string x) (String.concat ~sep:", " y)
  | ENeg _ -> Printf.sprintf "¬"
  | EAnd (_, _) -> Printf.sprintf "∧"
  | EOr (_, _) -> Printf.sprintf "∨"
  | EImp (_, _, _) -> Printf.sprintf "→"
  | EIff (_, _, _, _) -> Printf.sprintf "↔"
  | EExists (x, _) -> Printf.sprintf "∃ %s." x
  | EForall (x, _) -> Printf.sprintf "∀ %s." x
  | EPrev (i, _) -> Printf.sprintf "●%s" (Interval.to_string i)
  | ENext (i, _) -> Printf.sprintf "○%s" (Interval.to_string i)
  | EOnce (i, _) -> Printf.sprintf "⧫%s" (Interval.to_string i)
  | EEventually (i, _, _) -> Printf.sprintf "◊%s" (Interval.to_string i)
  | EHistorically (i, _) -> Printf.sprintf "■%s" (Interval.to_string i)
  | EAlways (i, _, _) -> Printf.sprintf "□%s" (Interval.to_string i)
  | ESince (_, i, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
  | EUntil (_, i, _,  _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
  | EType (_, _) -> Printf.sprintf ":"
and op_to_string f = op_to_string_core f.f


let rec to_string_core_rec l = function
  | ETT -> Printf.sprintf "⊤"
  | EFF -> Printf.sprintf "⊥"
  | EEqConst (x, (c, _)) -> Printf.sprintf "%s = %s" (ETerm.to_string x) (Dom.to_string c)
  | EPredicate (r, trms, _) -> Printf.sprintf "%s(%s)" r (ETerm.list_to_string trms)
  | EAgg (s, op, x, y, f) -> Printf.sprintf "%s = %s(%s; %s; %s)" s (Aggregation.op_to_string op) (ETerm.value_to_string x) (String.concat ~sep:", " y) (to_string_rec 5 f)
  | ENeg f -> Printf.sprintf "¬%a" (fun _ -> to_string_rec 5) f
  | EAnd (s, fs) ->
     let sep = "∧" ^ Side.to_string s in
     let strings = List.map fs ~f:(to_string_rec 4) in
     Util.paren_string l 4 (String.concat ~sep strings)
  | EOr (s, fs) ->
     let sep = "∨" ^ Side.to_string s in
     let strings = List.map fs ~f:(to_string_rec 4) in
     Util.paren_string l 3 (String.concat ~sep strings)
  | EImp (s, f, g) -> Printf.sprintf (Util.paren l 5 "%a →%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | EIff (s, t, f, g) -> Printf.sprintf (Util.paren l 5 "%a ↔%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string2) (s, t) (fun _ -> to_string_rec 5) g
  | EExists (x, f) -> Printf.sprintf (Util.paren l 5 "∃%s. %a") x (fun _ -> to_string_rec 5) f
  | EForall (x, f) -> Printf.sprintf (Util.paren l 5 "∀%s. %a") x (fun _ -> to_string_rec 5) f
  | EPrev (i, f) -> Printf.sprintf (Util.paren l 5 "●%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | ENext (i, f) -> Printf.sprintf (Util.paren l 5 "○%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | EOnce (i, f) -> Printf.sprintf (Util.paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | EEventually (i, _, f) -> Printf.sprintf (Util.paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | EHistorically (i, f) -> Printf.sprintf (Util.paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | EAlways (i, _, f) -> Printf.sprintf (Util.paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | ESince (s, i, f, g) -> Printf.sprintf (Util.paren l 0 "%a S%a%a %a") (fun _ -> to_string_rec 5) f
                         (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | EUntil (s, i, _, f, g) -> Printf.sprintf (Util.paren l 0 "%a U%a%a %a") (fun _ -> to_string_rec 5) f
                                (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | EType (f, ty) -> Printf.sprintf (Util.paren l 0 "%a : %a") (fun _ -> to_string_rec 5) f (fun _ -> ty_to_string) ty

and to_string_rec l form =
  if EnfType.equal form.enftype EnfType.Obs then
    Printf.sprintf "%a" (fun _ -> to_string_core_rec 5) form.f
  else
    Printf.sprintf (Util.paren l 0 "%a : %s") (fun _ -> to_string_core_rec 5) form.f (EnfType.to_string form.enftype)

let to_string = to_string_rec 0

let to_string_core = to_string_core_rec 0

let rec relative_interval (f: t) =
  match f.f with
  | ETT | EFF | EEqConst _ | EPredicate _ -> Zinterval.singleton 0
  | EAgg (_, _, _, _, f) -> Zinterval.to_zero (relative_interval f)
  | ENeg f | EExists (_, f) | EForall (_, f) -> relative_interval f
  | EAnd (_, fs) | EOr (_, fs)
    -> List.fold_left (List.map fs ~f:relative_interval) ~init:Zinterval.full ~f:Zinterval.lub
  | EImp (_, f1, f2) | EIff (_, _, f1, f2)
    -> Zinterval.lub (relative_interval f1) (relative_interval f2)
  | EPrev (i, f) | EOnce (i, f) | EHistorically (i, f)
    -> let i' = Zinterval.inv (Zinterval.of_interval i) in
       Zinterval.lub (Zinterval.to_zero i') (Zinterval.sum i' (relative_interval f))
  | ENext (i, f) | EEventually (i, _, f) | EAlways (i, _, f)
    -> let i = Zinterval.of_interval i in
       Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i (relative_interval f))
  | ESince (_, i, f1, f2) ->
     let i' = Zinterval.inv (Zinterval.of_interval i) in
     (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
        (Zinterval.sum i' (relative_interval f2)))
  | EUntil (_, i, _, f1, f2) ->
     let i' = Zinterval.of_interval i in
     (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
        (Zinterval.sum i' (relative_interval f2)))
  | EType (f, _) -> relative_interval f

let strict (f: t) =
  let rec _strict itv fut (f: t) =
    ((Zinterval.mem 0 itv) && fut)
    || (match f.f with
        | ETT | EFF | EEqConst (_, _) | EPredicate _-> false
        | ENeg f | EExists (_, f) | EForall (_, f) | EAgg (_, _, _, _, f) -> _strict itv fut f
        | EImp (_, f1, f2) | EIff (_, _, f1, f2)
          -> (_strict itv fut f1) || (_strict itv fut f2)
        | EAnd (_, fs) | EOr (_, fs)
          -> List.exists fs ~f:(_strict itv fut)
        | EPrev (i, f) | EOnce (i, f) | EHistorically (i, f)
          -> _strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f
        | ENext (i, f) | EEventually (i, _, f) | EAlways (i, _, f)
          -> _strict (Zinterval.sum (Zinterval.of_interval i) itv) true f
        | ESince (_, i, f1, f2)
          -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f1)
             || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f2)
        | EUntil (_, i, _, f1, f2)
          -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f1)
             || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f2)
        | EType (f, _) -> _strict itv fut f)
  in not (_strict (Zinterval.singleton 0) false f)

let relative_past (f: t) =
  Zinterval.is_nonpositive (relative_interval f)

let strictly_relative_past (f: t) =
  (relative_past f) && (strict f)

let rec is_transparent (f: t) = match f.enftype with
  | Cau -> begin
      match f.f with
      | ETT | EPredicate _ -> true
      | ENeg f | EExists (_, f) | EForall (_, f)
        | EOnce (_, f) | ENext (_, f) | EHistorically (_, f)
          | EAlways (_, _, f) -> is_transparent f
      | EEventually (_, b, f) -> b && is_transparent f
      | EImp (L, f, g) | EIff (L, L, f, g) -> is_transparent f && strictly_relative_past g
      | EOr (L, f :: fs) -> is_transparent f && List.for_all fs ~f:strictly_relative_past
      | EImp (R, f, g) | EIff (R, R, f, g) -> is_transparent g && strictly_relative_past f
      | EOr (R, fs) -> is_transparent (List.last_exn fs) && List.for_all (List.drop_last_exn fs) ~f:strictly_relative_past
      | EAnd (_, fs) -> List.for_all fs ~f:is_transparent
      | EIff (_, _, f, g) -> is_transparent f && is_transparent g
      | ESince (_, _, f, g) -> is_transparent f && strictly_relative_past g
      | EUntil (R, _, b, f, g) -> b && is_transparent f && strictly_relative_past g
      | EUntil (LR, _, b, f, g) -> b && is_transparent f && is_transparent g
      | _ -> false
    end
  | Sup -> begin
      match f.f with
      | EFF | EPredicate _ -> true
      | ENeg f | EExists (_, f) | EForall (_, f)
        | EOnce (_, f) | ENext (_, f) | EHistorically (_, f)
        | EEventually (_, _, f) -> is_transparent f
      | EAlways (_, b, f) -> b && is_transparent f
      | EAnd (L, f :: fs) -> is_transparent f && List.for_all fs ~f:strictly_relative_past
      | EIff (L, L, f, g) -> is_transparent f && strictly_relative_past g
      | EIff (R, R, f, g) -> is_transparent g && strictly_relative_past f
      | EAnd (R, fs) -> is_transparent (List.last_exn fs) && List.for_all (List.drop_last_exn fs) ~f:strictly_relative_past
      | EIff (_, _, f, g) -> is_transparent f && is_transparent g
      | EOr (_, fs) -> List.for_all fs ~f:is_transparent
      | ESince (L, _, f, g) -> is_transparent f && strictly_relative_past g
      | ESince (R, _, f, g) -> is_transparent f && is_transparent g
      | EUntil (R, _, _, f, g) -> is_transparent f && strictly_relative_past g
      | EUntil (_, _, _, f, g) -> is_transparent g && strictly_relative_past f
      | _ -> false
    end
  | _ -> assert false