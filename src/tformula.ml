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



type tinfo_type = {
    pos: LexingInfo.t;
    event_type_opt: Lex.event_type option;
  } [@@deriving compare, sexp_of, hash, equal]

module Info : MFOTL_lib.Modules.I with type t = tinfo_type = struct
  
  type t = tinfo_type [@@deriving compare, sexp_of, hash, equal]

  let to_string _ s _ = s
    (* "{ " ^ s ^ "; t_vars = " ^ String.concat ~sep:", " (List.map ~f:(fun (k, v) -> k ^ " -> " ^ TypeTerm.to_string v) info.t_vars) ^ " }"*)
  
  let dummy = { pos = LexingInfo.dummy; event_type_opt = None }

end

include MFOTL_lib.MFOTL.Make(Info)(Term.StringVar)(Dom)(TTerm)

module StringMap = Map.Make(String)

let rec to_formula (f: t): Formula.t =
  Formula.make (to_formula_core f.form) { pos = f.info.pos }

and to_formula_core: core_t -> Formula.core_t =
  function
  | TT -> TT
  | FF -> FF
  | EqConst (trm, c) -> EqConst (TTerm.to_term trm, c)
  | Predicate (e, trms) -> Predicate (e, List.map trms ~f:TTerm.to_term)
  | Predicate' (e, trms, f) -> Predicate' (e, List.map trms ~f:TTerm.to_term, to_formula f)
  | Let (s, ty_opt, vars, f, g) -> Let (s, ty_opt, vars, to_formula f, to_formula g)
  | Let' (s, ty_opt, vars, f, g) -> Let' (s, ty_opt, vars, to_formula f, to_formula g)
  | Agg (s, op, x, y, f) -> Agg (s, op, TTerm.to_term x, y, to_formula f)
  | Top (s, op, x, y, f) -> Top (s, op, List.map ~f:TTerm.to_term x, y, to_formula f)
  | Neg f -> Neg (to_formula f)
  | And (s, fs) -> And (s, List.map fs ~f:to_formula)
  | Or (s, fs) -> Or (s, List.map fs ~f:to_formula)
  | Imp (s, f, g) -> Imp (s, to_formula f, to_formula g)
  | Exists (x, f) -> Exists (x, to_formula f)
  | Forall (x, f) -> Forall (x, to_formula f)
  | Prev (i, f) -> Prev (i, to_formula f)
  | Next (i, f) -> Next (i, to_formula f)
  | Once (i, f) -> Once (i, to_formula f)
  | Eventually (i, f) -> Eventually (i, to_formula f)
  | Historically (i, f) -> Historically (i, to_formula f)
  | Always (i, f) -> Always (i, to_formula f)
  | Since (s, i, f, g) -> Since (s, i, to_formula f, to_formula g)
  | Until (s, i, f, g) -> Until (s, i, to_formula f, to_formula g)
  | Type (f, ty) -> Type (to_formula f, ty)
  | Label (s, f) -> Label (s, to_formula f)
