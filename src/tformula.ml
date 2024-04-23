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

type core_t =
  | TTT
  | TFF
  | TEqConst of string * Dom.t
  | TPredicate of string * Term.t list
  | TNeg of t
  | TAnd of Side.t * t * t
  | TOr of Side.t * t * t
  | TImp of Side.t * t * t
  | TIff of Side.t * Side.t * t * t
  | TExists of string * t
  | TForall of string * t
  | TPrev of Interval.t * t
  | TNext of Interval.t * t
  | TOnce of Interval.t * t
  | TEventually of Interval.t * bool * t
  | THistorically of Interval.t * t
  | TAlways of Interval.t * bool * t
  | TSince of Side.t * Interval.t * t * t
  | TUntil of Side.t * Interval.t * bool * t * t
  | TType of t * ty

and t = { f: core_t; enftype: EnfType.t; id: int }

let make f enftype id = { f; enftype; id }

let ttt = TTT
let fff = TFF
let teqconst x d = TEqConst (x, d)
let tpredicate p_name trms = TPredicate (p_name, trms)
let tneg f = TNeg f
let tconj s f g = TAnd (s, f, g)
let tdisj s f g = TOr (s, f, g)
let timp s f g = TImp (s, f, g)
let tiff s t f g = TIff (s, t, f, g)
let texists x f = TExists (x, f)
let tforall x f = TForall (x, f)
let tprev i f = TPrev (i, f)
let tnext i f = TNext (i, f)
let tonce i f = TOnce (i, f)
let teventually i f = TEventually (i, true, f)
let thistorically i f = THistorically (i, f)
let talways i f = TAlways (i, true, f)
let tsince s i f g = TSince (s, i, f, g)
let tuntil s i f g = TUntil (s, i, true, f, g)
let ttype s t = TType (s, t)

let tbigcauconj = function
  | [] -> make ttt Non 0
  | h::t -> List.fold_left t ~init:h ~f:(fun f g -> make (tconj N f g) Non 0)

let tbigcauforall vars f =
  List.fold_right vars ~init:f ~f:(fun x f -> make (tforall x f) Non 0)

let rec core_of_formula ?id:(id=1) =
  let lof_formula = of_formula ~id:(2*id)
  and rof_formula = of_formula ~id:(2*id+1) in
  function
  | TT -> TTT
  | FF -> TFF
  | EqConst (x, v) -> TEqConst (x, v)
  | Predicate (e, t) -> TPredicate (e, t)
  | Neg f -> TNeg (lof_formula f)
  | And (s, f, g) -> TAnd (s, lof_formula f, rof_formula g)
  | Or (s, f, g) -> TOr (s, lof_formula f, rof_formula g)
  | Imp (s, f, g) -> TImp (s, lof_formula f, rof_formula g)
  | Iff (s, t, f, g) -> TIff (s, t, lof_formula f, rof_formula g)
  | Exists (x, f) -> TExists (x, lof_formula f)
  | Forall (x, f) -> TForall (x, lof_formula f)
  | Prev (i, f) -> TPrev (i, lof_formula f)
  | Next (i, f) -> TNext (i, lof_formula f)
  | Once (i, f) -> TOnce (i, lof_formula f)
  | Eventually (i, f) -> TEventually (i, true, lof_formula f)
  | Historically (i, f) -> THistorically (i, lof_formula f)
  | Always (i, f) -> TAlways (i, true, lof_formula f)
  | Since (s, i, f, g) -> TSince (s, i, lof_formula f, rof_formula g)
  | Until (s, i, f, g) -> TUntil (s, i, true, lof_formula f, rof_formula g)
  | Type (f, ty) -> TType (lof_formula f, ty)

and of_formula ?id:(id=1) f = { f = core_of_formula ~id f; enftype = EnfType.Obs; id }

let rec fv f = match f.f with
  | TTT | TFF -> Set.empty (module String)
  | TEqConst (x, _) -> Set.of_list (module String) [x]
  | TPredicate (_, trms) -> Set.of_list (module String) (Term.fv_list trms)
  | TExists (x, f)
    | TForall (x, f) -> Set.filter (fv f) ~f:(fun y -> not (String.equal x y))
  | TNeg f
    | TPrev (_, f)
    | TOnce (_, f)
    | THistorically (_, f) 
    | TEventually (_, _, f)
    | TAlways (_, _, f)
    | TNext (_, f)
    | TType (f, _) -> fv f
  | TAnd (_, f1, f2)
    | TOr (_, f1, f2)
    | TImp (_, f1, f2)
    | TIff (_, _, f1, f2)
    | TSince (_, _, f1, f2)
    | TUntil (_, _, _, f1, f2) -> Set.union (fv f1) (fv f2)

let rec rank = function
  | TTT | TFF -> 0
  | TEqConst _ -> 0
  | TPredicate (_, args) -> List.length args
  | TNeg f
    | TExists (_, f)
    | TForall (_, f)
    | TPrev (_, f)
    | TNext (_, f)
    | TOnce (_, f)
    | TEventually (_, _, f)
    | THistorically (_, f)
    | TAlways (_, _, f)
    | TType (f, _) -> rank f.f
  | TAnd (_, f, g)
    | TOr (_, f, g)
    | TImp (_, f, g)
    | TIff (_, _, f, g)
    | TSince (_, _, f, g)
    | TUntil (_, _, _, f, g) -> rank f.f + rank g.f

let fix_side s f g =
  match s with
  | Side.LR -> if rank f < rank g then Side.L
               else Side.R
  | _ -> s

let rec to_formula f = match f.f with
  | TTT -> TT
  | TFF -> FF
  | TEqConst (x, v) -> EqConst (x, v)
  | TPredicate (e, t) -> Predicate (e, t)
  | TNeg f -> Neg (to_formula f)
  | TAnd (s, f, g) -> And (fix_side s f.f g.f, to_formula f, to_formula g)
  | TOr (s, f, g) -> Or (fix_side s f.f g.f, to_formula f, to_formula g)
  | TImp (s, f, g) -> Imp (fix_side s f.f g.f, to_formula f, to_formula g)
  | TIff (s, t, f, g) -> Iff (fix_side s f.f g.f, fix_side t f.f g.f, to_formula f, to_formula g)
  | TExists (x, f) -> Exists (x, to_formula f)
  | TForall (x, f) -> Forall (x, to_formula f)
  | TPrev (i, f) -> Prev (i, to_formula f)
  | TNext (i, f) -> Next (i, to_formula f)
  | TOnce (i, f) -> Once (i, to_formula f)
  | TEventually (i, _, f) -> Eventually (i, to_formula f)
  | THistorically (i, f) -> Historically (i, to_formula f)
  | TAlways (i, _, f) -> Always (i, to_formula f)
  | TSince (s, i, f, g) -> Since (fix_side s f.f g.f, i, to_formula f, to_formula g)
  | TUntil (s, i, _, f, g) -> Until (s, i, to_formula f, to_formula g)
  | TType (f, ty) -> Type (to_formula f, ty)

let rec op_to_string_core = function
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst _ -> Printf.sprintf "="
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TNeg _ -> Printf.sprintf "¬"
  | TAnd (_, _, _) -> Printf.sprintf "∧"
  | TOr (_, _, _) -> Printf.sprintf "∨"
  | TImp (_, _, _) -> Printf.sprintf "→"
  | TIff (_, _, _, _) -> Printf.sprintf "↔"
  | TExists (x, _) -> Printf.sprintf "∃ %s." x
  | TForall (x, _) -> Printf.sprintf "∀ %s." x
  | TPrev (i, _) -> Printf.sprintf "●%s" (Interval.to_string i)
  | TNext (i, _) -> Printf.sprintf "○%s" (Interval.to_string i)
  | TOnce (i, _) -> Printf.sprintf "⧫%s" (Interval.to_string i)
  | TEventually (i, _, _) -> Printf.sprintf "◊%s" (Interval.to_string i)
  | THistorically (i, _) -> Printf.sprintf "■%s" (Interval.to_string i)
  | TAlways (i, _, _) -> Printf.sprintf "□%s" (Interval.to_string i)
  | TSince (_, i, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
  | TUntil (_, i, _,  _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
  | TType (_, _) -> Printf.sprintf ":"
and op_to_string f = op_to_string_core f.f


let rec to_string_core_rec l = function
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst (x, c) -> Printf.sprintf "%s = %s" x (Dom.to_string c)
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TNeg f -> Printf.sprintf "¬%a" (fun _ -> to_string_rec 5) f
  | TAnd (s, f, g) -> Printf.sprintf (Util.paren l 4 "%a ∧%a %a") (fun _ -> to_string_rec 4) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 4) g
  | TOr (s, f, g) -> Printf.sprintf (Util.paren l 3 "%a ∨%a %a") (fun _ -> to_string_rec 3) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 4) g
  | TImp (s, f, g) -> Printf.sprintf (Util.paren l 5 "%a →%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | TIff (s, t, f, g) -> Printf.sprintf (Util.paren l 5 "%a ↔%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string2) (s, t) (fun _ -> to_string_rec 5) g
  | TExists (x, f) -> Printf.sprintf (Util.paren l 5 "∃%s. %a") x (fun _ -> to_string_rec 5) f
  | TForall (x, f) -> Printf.sprintf (Util.paren l 5 "∀%s. %a") x (fun _ -> to_string_rec 5) f
  | TPrev (i, f) -> Printf.sprintf (Util.paren l 5 "●%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TNext (i, f) -> Printf.sprintf (Util.paren l 5 "○%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TOnce (i, f) -> Printf.sprintf (Util.paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TEventually (i, _, f) -> Printf.sprintf (Util.paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | THistorically (i, f) -> Printf.sprintf (Util.paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TAlways (i, _, f) -> Printf.sprintf (Util.paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TSince (s, i, f, g) -> Printf.sprintf (Util.paren l 0 "%a S%a%a %a") (fun _ -> to_string_rec 5) f
                         (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | TUntil (s, i, _, f, g) -> Printf.sprintf (Util.paren l 0 "%a U%a%a %a") (fun _ -> to_string_rec 5) f
                                (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | TType (f, ty) -> Printf.sprintf (Util.paren l 0 "%a : %a") (fun _ -> to_string_rec 5) f (fun _ -> ty_to_string) ty

and to_string_rec l form =
  if EnfType.equal form.enftype EnfType.Obs then
    Printf.sprintf "%a" (fun _ -> to_string_core_rec 5) form.f
  else
    Printf.sprintf (Util.paren l 0 "%a : %s") (fun _ -> to_string_core_rec 5) form.f (EnfType.to_string form.enftype)

let to_string = to_string_rec 0

let to_string_core = to_string_core_rec 0
