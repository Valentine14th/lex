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

module Term = Tformula.Term

type core_t =
  | ETT
  | EFF
  | EEqConst of Term.t * Dom.t
  | EPredicate of string * Term.t list * Lex.event_type
  | EAgg of string * Aggregation.op * Term.t * string list * t
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

and t = { f: core_t; enftype: EnfType.t; id: int }

let make f enftype id = { f; enftype; id }

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
  | [] -> make ett Non 0
  | h::t -> List.fold_left t ~init:h ~f:(fun f g -> make (econj N f g) Non 0)
(*TODO: assign correct type to formula, not just Non*)

let tbigcauforall vars f =
  List.fold_right vars ~init:f ~f:(fun x f -> make (eforall x f) Non 0)

let rec core_of_tformula tevents ?id:(id=1) d = 
  let lof_formula = of_tformula tevents ~id:(d*id)
  and rof_formula = of_tformula tevents ~id:(d*id+1)
  and iof_formula i = of_tformula tevents ~id:(d*id+i) in
  function
  | Tformula.TTT -> ETT
  | TFF -> EFF
  | TEqConst (x, y) -> 
     (if Term.equal_core y.trm (Term.TConst (Dom.Bool true)) then
       EEqConst (x, Dom.Bool true)
     else
       EEqConst ({ trm = Term.TBinop (x, Formula.Term.BEq, y);
                   tt = TypeTerm.TypeConst (Dom.TBool) },
                 Dom.Bool true))
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

and of_tformula tevents ?id:(id=1) f =
  let d = Tformula.deg f in
  { f = core_of_tformula tevents ~id d f; enftype = EnfType.Obs; id }

let of_tformulas tevents = List.map ~f:(of_tformula tevents)

let rec fv f = match f.f with
  | ETT | EFF -> Set.empty (module String)
  | EEqConst (x, _) -> Set.of_list (module String) (Term.fv_list [x])
  | EPredicate (_, trms, _) -> Set.of_list (module String) (Term.fv_list trms)
  | EAgg (s, _, _, y, _) -> Set.of_list (module String) (s :: y)
  | EExists (x, f)
    | EForall (x, f) -> Set.filter (fv f) ~f:(fun y -> not (String.equal x y))
  | ENeg f
    | EPrev (_, f)
    | EOnce (_, f)
    | EHistorically (_, f) 
    | EEventually (_, _, f)
    | EAlways (_, _, f)
    | ENext (_, f)
    | EType (f, _) -> fv f
    | EImp (_, f1, f2)
    | EIff (_, _, f1, f2)
    | ESince (_, _, f1, f2)
    | EUntil (_, _, _, f1, f2) -> Set.union (fv f1) (fv f2)
  | EAnd (_, fs)
    | EOr (_, fs) ->
     let f x g = Set.union x (fv g) in
     List.fold_left fs ~init:(Set.empty (module String)) ~f

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

let rec to_formula f = to_formula_core f.f

and to_formula_core = function
  | ETT -> TT
  | EFF -> FF
  | EEqConst (trm, c) -> Term (Formula.Term.Binop (Term.to_formula_term trm, Formula.Term.BEq, Formula.Term.Const c))
  | EPredicate (e, trms, _) -> Predicate (e, List.map trms ~f:Term.to_formula_term)
  | EAgg (s, op, x, y, f) -> Agg (s, op, Term.to_formula_term x, y, to_formula f)
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
  | EPredicate (r, trms, _) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | EAgg (_, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" (Aggregation.op_to_string op) (Term.value_to_string x) (String.concat ~sep:", " y)
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
  | EEqConst (x, c) -> Printf.sprintf "%s = %s" (Term.to_string x) (Dom.to_string c)
  | EPredicate (r, trms, _) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | EAgg (s, op, x, y, f) -> Printf.sprintf "%s = %s(%s; %s; %s)" s (Aggregation.op_to_string op) (Term.value_to_string x) (String.concat ~sep:", " y) (to_string_rec 5 f)
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
