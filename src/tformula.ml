
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
module Side = MFOTL_lib.Side

module StringVar = Term.StringVar

type tinfo_type = {
    pos: LexingInfo.t;
    event_type_opt: Lex.event_type option;
    t_vars: (string * TypeTerm.t) list;
  } [@@deriving compare, sexp_of, hash, equal]

module Info : MFOTL_lib.Modules.I with type t = tinfo_type = struct
  
  type t = tinfo_type [@@deriving compare, sexp_of, hash, equal]

  let to_string _ s _ = s
    (* "{ " ^ s ^ "; t_vars = " ^ String.concat ~sep:", " (List.map ~f:(fun (k, v) -> k ^ " -> " ^ TypeTerm.to_string v) info.t_vars) ^ " }"*)
  
  let dummy = { pos = LexingInfo.dummy; event_type_opt = None; t_vars = [] }

end

include MFOTL_lib.MFOTL.Make(Info)(StringVar)(Dom)(TTerm)

module StringMap = Map.Make(String)

(*
let fix_side s f g =
  match s with
  | Side.LR -> if rank f < rank g then Side.L
               else Side.R
  | _ -> s

let rec to_formula (f: t): Formula.t = match f.form with
  | TT -> Formula.tt
  | FF -> ff f.pos
  | TEqConst (trm, trm') ->
    term f.pos (Term.binop f.pos (TTerm.to_formula_term trm) Term.BEq (TTerm.to_formula_term trm'))
  | TPredicate (e, trms, _) -> predicate f.pos e (List.map trms ~f:TTerm.to_formula_term)
  | TAgg (s, op, x, y, g) -> agg f.pos s op (TTerm.to_formula_term x) y (to_formula g)
  | TNeg g -> neg f.pos (to_formula g)
  | TAnd (s, fs) -> conj' f.pos (fix_side s (List.hd_exn fs) (List.last_exn fs)) (List.map fs ~f:to_formula)
  | TOr (s, fs) -> disj' f.pos (fix_side s (List.hd_exn fs) (List.last_exn fs)) (List.map fs ~f:to_formula)
  | TImp (s, g, h) -> imp f.pos (fix_side s g h) (to_formula g) (to_formula h)
  | TIff (s2, g, h) -> iff f.pos ((fix_side (fst s2) g h, fix_side (snd s2) g h)) (to_formula g) (to_formula h)
  | TExists (x, g) -> exists f.pos x (to_formula g)
  | TForall (x, g) -> forall f.pos x (to_formula g)
  | TPrev (i, g) -> prev f.pos i (to_formula g)
  | TNext (i, g) -> next f.pos i (to_formula g)
  | TOnce (i, g) -> once f.pos i (to_formula g)
  | TEventually (i, g) -> eventually f.pos i (to_formula g)
  | THistorically (i, g) -> historically f.pos i (to_formula g)
  | TAlways (i, g) -> always f.pos i (to_formula g)
  | TSince (s, i, g, h) -> since f.pos (fix_side s g h) i (to_formula g) (to_formula h)
  | TUntil (s, i, g, h) -> until f.pos s i (to_formula g) (to_formula h)
  | TType (g, ty) -> type_ f.pos (to_formula g) ty
 *)

