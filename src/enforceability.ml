(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base
open Core

open Formula
open Tformula
open Tlex
open Elex

let rec is_past_guarded s x p f =
  let r =
  match f with
  | TTT | TFF -> false
  | TEqConst (x', y) -> p && Term.equal_core (Term.TVar x) x'.trm && Term.is_const y.trm
  | TPredicate (_, ts, _) -> List.exists ~f:(fun t -> Term.equal_core (Term.TVar x) t.trm) ts
  | TAgg (_, _, _, y, f) -> List.mem y x ~equal:String.equal && is_past_guarded s x p f
  | TNeg f -> is_past_guarded s x (not p) f
  | TAnd (_, fs) when p -> List.exists fs ~f:(is_past_guarded s x p)
  | TAnd (_, fs) -> List.for_all fs ~f:(is_past_guarded s x p)
  | TOr (_, fs) when p -> List.for_all fs ~f:(is_past_guarded s x p)
  | TOr (_, fs) -> List.exists fs ~f:(is_past_guarded s x p)
  | TImp (_, f, g) when p -> is_past_guarded s x (not p) f && is_past_guarded s x p g
  | TImp (_, f, g) -> is_past_guarded s x (not p) f || is_past_guarded s x p g
  | TIff (_, _, f, g) when p -> is_past_guarded s x (not p) f && is_past_guarded s x p g
                               || is_past_guarded s x p f && is_past_guarded s x (not p) g
  | TIff (_, _, f, g) -> (is_past_guarded s x (not p) f || is_past_guarded s x p g)
                        && (is_past_guarded s x p f || is_past_guarded s x (not p) g)
  | TExists (y, f) | TForall (y, f) -> not (String.equal x y) && is_past_guarded s x p f
  | TPrev (_, f) -> p && is_past_guarded s x p f
  | TOnce (_, f) | TEventually (_, f) when p -> is_past_guarded s x p f
  | TOnce (i, f) | TEventually (i, f) -> Interval.has_zero i && is_past_guarded s x p f
  | THistorically (_, f) | TAlways (_, f) when not p -> is_past_guarded s x p f
  | THistorically (i, f) -> Interval.has_zero i && is_past_guarded s x p f
  | TSince (_, i, f, g) when p -> not (Interval.has_zero i) && is_past_guarded s x p f
                                 || is_past_guarded s x p g
  | TUntil (_, i, f, g) when p -> not (Interval.has_zero i) && is_past_guarded s x p f
                                 || is_past_guarded s x p f && is_past_guarded s x p g
  | TSince (_, i, _, g) | TUntil (_, i, _, g) -> Interval.has_zero i && is_past_guarded s x p g
  | _ -> false
  in r

module Errors = struct

  type error =
    | ECast of string * EnfType.t * bool * EnfType.t * bool
    | EFormula of Lexing.position * string option * t * EnfType.t
    | EFormulaTransparent of Lexing.position * string option * t * EnfType.t
    | EFormulasTransparent of Lexing.position * (string * string) option * t list * EnfType.t
    | EConj of error * error
    | EDisj of error * error
    | EInit of Lexing.position option
    | EPattern of Lexing.position * string * tpattern * (Lexing.position * Tformula.t) list * EnfType.t
    | ERule of Lexing.position * string

  let rec to_string ?(n=0) e =
    let sp = Util.spaces (2*n) in
    let lb = "\n" ^ sp in
    begin match e with
      | ECast (e, t', _, t, false) -> Printf.sprintf "make %s %s (currently, it has type %s)"
                              e (EnfType.to_string t) (EnfType.to_string t')
      | ECast (e, t', false, t, true) -> Printf.sprintf "make %s %s:Transparent (currently, it has type %s, transparency is not the issue as it gets assumed)"
                              e (EnfType.to_string t) (EnfType.to_string t')
      | ECast (e, t', true, t, true) -> Printf.sprintf "make %s %s:Transparent (currently, it has type %s:Transparent)"
                              e (EnfType.to_string t) (EnfType.to_string t')
      | EFormula (pos, None, f, t) -> Printf.sprintf "make %s %s, but this is impossible at %s"
                                    (Tformula.to_string f) (EnfType.to_string t) (Util.string_of_pos pos)
      | EFormula (pos, Some s, f, t) -> Printf.sprintf "make %s %s, but this is impossible (%s) at %s"
                                      (Tformula.to_string f) (EnfType.to_string t) s (Util.string_of_pos pos)
      | EFormulaTransparent (pos, None, f, t) -> Printf.sprintf "make %s %s, but this is impossible at %s"
                                    (Tformula.to_string f) (EnfType.to_string t) (Util.string_of_pos pos)
      | EFormulaTransparent (pos, Some s, f, t) -> Printf.sprintf "make %s %s, but this is impossible (%s) at %s"
                                      (Tformula.to_string f) (EnfType.to_string t) s (Util.string_of_pos pos)
      | EFormulasTransparent (pos, None, fs, t) -> Printf.sprintf "make %s %s, but this is impossible at %s"
                                    (List.map ~f:Tformula.to_string fs |> Util.string_of_string_list) (EnfType.to_string t) (Util.string_of_pos pos)
      | EFormulasTransparent (pos, Some (op, s), fs, t) -> Printf.sprintf "make %s (%s) %s, but this is impossible (%s) at %s"
                                      (List.map ~f:Tformula.to_string fs |> Util.string_of_string_list) op (EnfType.to_string t) s (Util.string_of_pos pos)
      | EConj (f, g) -> Printf.sprintf "both%s* %s%sand%s* %s"
                          lb (to_string ~n:(n+1) f) lb lb (to_string ~n:(n+1) g)
      | EDisj (f, g) -> Printf.sprintf "either%s* %s%sor%s* %s"
                          lb (to_string ~n:(n+1) f) lb lb (to_string ~n:(n+1) g)
      | EInit (Some pos) -> Util.string_of_pos pos
      | EInit None -> ""
      | EPattern (pos, msg, p, _, t) -> Printf.sprintf "make %s %s, but this is impossible at %s because of %s" (* TODO: incorporate formual list in error message *)
                                  (string_of_tpattern p) (EnfType.to_string t) (Util.string_of_pos pos) msg
      | ERule (pos, msg) -> Printf.sprintf "%s at %s" msg (Util.string_of_pos pos)
    end
end

module Constraints = struct

  type constr =
    | CTT
    | CFF
    | CEq of string * EnfType.t * bool
    | CConj of constr * constr
    | CDisj of constr * constr [@@deriving compare, sexp_of]

  let rec equal c c' = match c, c' with
    | CTT, CTT -> true
    | CFF, CFF -> true
    | CEq (s, ty, tr), CEq (s', ty', tr') -> String.equal s s' && EnfType.equal ty ty' && Bool.equal tr tr'
    | CConj (c1, c2), CConj (c1', c2') -> equal c1 c1' && equal c2 c2'
    | CDisj (c1, c2), CDisj (c1', c2') -> equal c1 c1' && equal c2 c2'
    | _, _ -> false

  type verdict = Possible of constr | Impossible of Errors.error

  let tt = CTT
  let ff = CFF
  let eq s t tr = CEq (s, t, tr)

  let conj c d = match c, d with
    | Possible CTT, _ -> d
    | _, Possible CTT -> c
    | Impossible c, Impossible d -> Impossible (EConj (c, d))
    | Impossible c, _ | _, Impossible c -> Impossible c
    | Possible c, Possible d -> Possible (CConj (c, d))

  let disj c d = match c, d with
    | Impossible c, Impossible d -> Impossible (EDisj (c, d))
    | Impossible _, _ -> d
    | _, Impossible _ -> c
    | Possible CTT, _ | _, Possible CTT -> Possible CTT
    | Possible c, Possible d -> Possible (CDisj (c, d))

  let rec cartesian a = function
      [] -> []
    | h::t -> (List.map a ~f:(fun x -> (x,h))) @ cartesian a t

  exception CannotMerge

  let merge_aux ~key:_ = function
    | `Left (t, tr) | `Right (t, tr) -> Some (t, tr)
    | `Both ((t, tr), (t', tr')) ->
      if EnfType.equal t t' then
        Some (t, tr || tr') (* TODO: should merging also only be allowed if the transparency values are the same? *)
      else
        raise CannotMerge

  let try_merge (a, b) =
    try Some (Map.merge a b ~f:merge_aux)
    with CannotMerge -> None

  let rec solve = function
    | CTT -> [Map.empty (module String)]
    | CFF -> []
    | CEq (s, t, tr) -> [Map.singleton (module String) s (t, tr)]
    | CConj (c, d) -> List.filter_map (cartesian (solve c) (solve d)) ~f:try_merge
    | CDisj (c, d) -> (solve c) @ (solve d)

  (** Disjunctive normal form *)
  let dnf c = solve c
              |> List.map ~f:(fun m -> Map.to_alist m
              |> List.fold ~init:CTT ~f:(fun c (e, (t, tr)) -> CConj (c, CEq (e, t, tr))))

  let rec to_string_rec l = function
    | CTT -> Printf.sprintf "⊤"
    | CFF -> Printf.sprintf "⊥"
    | CEq (s, t, false) -> Printf.sprintf "t(%s) = %s" s (EnfType.to_string t)
    | CEq (s, t, true) -> Printf.sprintf "t(%s) = %s:Transparent" s (EnfType.to_string t) (* TODO: How to properly show that a predicate/event must be transparent (is only really applicable to institutional facts that are defined by let bindings)*)
    | CConj (c, d) -> Printf.sprintf (Util.paren l 4 "%a ∧ %a") (fun _ -> to_string_rec 4) c (fun _ -> to_string_rec 4) d
    | CDisj (c, d) -> Printf.sprintf (Util.paren l 3 "%a ∨ %a") (fun _ -> to_string_rec 3) c (fun _ -> to_string_rec 4) d

  let to_string = to_string_rec 0

end

open EnfType
open Constraints
open Option

(* todo: ensure that there is no shadowing *)

let types_predicate tr pols t e =
  (* TODO: verify that this function works correctly and makes use of the correct assumptions *)
  match Map.find pols e with
    | Some (t', tr') when EnfType.equal t t' && Bool.equal tr tr' -> Possible CTT
    | Some (t', tr') when EnfType.leq t t' -> Possible (eq e t (tr || tr'))
    | Some (t', tr') -> Impossible (ECast (e, t', tr', t, tr))
    | None -> Impossible (ECast (e, Non, false, t, tr))

let add_pos pos fs =
  List.map fs ~f:(fun f -> (pos, f))

let rec types s pols (t: EnfType.t) ((pos, f): (Lexing.position * Tformula.t)) =
  let error pos s = Impossible (EFormula (pos, Some s, f, t)) in
  let types_predicate = types_predicate false in (* set transparency requirement to false *)
  let types = types s pols in (* fix `types` function with invariant parameters *)
  match t with
  | Cau -> begin
      match f with
      | TTT -> Possible CTT
      | TPredicate (e, _, _) -> types_predicate pols Cau e
      | TNeg f -> types Sup (pos, f)
      | TAnd (_, fs) -> List.fold_left (List.map (add_pos pos fs) ~f:(types Cau)) ~init:(Possible CTT) ~f:conj
      | TOr (L, fs) -> types Cau (pos, List.hd_exn fs)
      | TOr (R, fs) -> types Cau (pos, List.last_exn fs)
      | TOr (_, fs) -> List.fold_left (List.map (add_pos pos fs) ~f:(types Cau)) ~init:(Possible CTT) ~f:disj
      | TImp (L, f, _) -> types Sup (pos, f)
      | TImp (R, _, g) -> types Cau (pos, g)
      | TImp (_, f, g) -> disj (types Sup (pos, f)) (types Cau (pos, g))
      | TIff (L, L, f, _) -> conj (types Sup (pos, f)) (types Cau (pos, f))
      | TIff (L, R, f, g) -> conj (types Sup (pos, f)) (types Sup (pos, g))
      | TIff (R, L, f, g) -> conj (types Cau (pos, g)) (types Cau (pos, f))
      | TIff (R, R, _, g) -> conj (types Cau (pos, g)) (types Sup (pos, g))
      | TIff (_, _, f, g) -> conj (disj (types Sup (pos, f)) (types Cau (pos, g)))
                                  (disj (types Cau (pos, f)) (types Sup (pos, g)))
      | TExists (_, f) -> types Cau (pos, f)
      | TForall (x, f) when is_past_guarded s x false f -> types Cau (pos, f)
      | TForall (x, _) -> error pos ("for causability " ^ x ^ " must be past-guarded")
      | TNext (i, f) when Interval.equal i Interval.full -> types Cau (pos, f)
      | TNext _ -> error pos "○ with non-[0,∞) interval is never Cau"
      | TOnce (i, g) | TSince (_, i, _, g) when Interval.has_zero i -> types Cau (pos, g)
      | TOnce _ | TSince _ -> error pos "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      | TEventually (_, f) | TAlways (_, f) -> types Cau (pos, f)
      | TUntil (LR, B _, f, g) -> conj (types Cau (pos, f)) (types Cau (pos, g))
      | TUntil (_, i, _, g) when Interval.has_zero i -> types Cau (pos, g) (* in the non-transparent case when i is unbounded, an artificial bound will be added during conversion *)
      | TUntil (_, _, f, g) -> conj (types Cau (pos, f)) (types Cau (pos, g)) (* in the non-transparent case when i is unbounded, an artificial bound will be added during conversion *)
      | TPrev _ -> error pos "● is never Cau"
      | _ -> Impossible (EFormula (pos, None, f, t))
    end
  | Sup -> begin
      match f with
      | TFF -> Possible CTT
      | TPredicate (e, _, _) -> types_predicate pols Sup e
      | TNeg f -> types Cau (pos, f)
      | TAnd (L, fs) -> types Sup (pos, List.hd_exn fs)
      | TAnd (R, fs) -> types Sup (pos, List.last_exn fs)
      | TAnd (_, fs) -> List.fold_left (List.map (add_pos pos fs) ~f:(types Sup)) ~init:(Possible CTT) ~f:disj
      | TOr (_, fs) -> List.fold_left (List.map (add_pos pos fs) ~f:(types Sup)) ~init:(Possible CTT) ~f:conj
      | TImp (_, f, g) -> conj (types Cau (pos, f)) (types Sup (pos, g))
      | TIff (L, _, f, g) -> conj (types Cau (pos, f)) (types Sup (pos, g))
      | TIff (R, _, f, g) -> conj (types Sup (pos, f)) (types Cau (pos, g))
      | TIff (_, _, f, g) -> disj (conj (types Cau (pos, f)) (types Sup (pos, g)))
                                  (conj (types Sup (pos, f)) (types Cau (pos, g)))
      | TExists (x, f) when is_past_guarded s x true f -> types Sup (pos, f)
      | TExists (x, _) -> error pos ("for suppressability " ^ x ^ " must be past-guarded")
      | TForall (_, f) -> types Sup (pos, f)
      | TNext (_, f) -> types Sup (pos, f)
      | THistorically (i, f) when Interval.has_zero i -> types Sup (pos, f)
      | THistorically _ -> error pos "■[a,b) with a > 0 is never Sup"
      | TSince (_, i, f, _) when not (Interval.has_zero i) -> types Sup (pos, f)
      | TSince (_, _, f, g) -> conj (types Sup (pos, f)) (types Sup (pos, g))
      | TEventually (_, f) | TAlways (_, f) -> types Sup (pos, f)
      | TUntil (L, i, f, _) when not (Interval.has_zero i) -> types Sup (pos, f)
      | TUntil (R, _, _, g) -> types Sup (pos, g)
      | TUntil (_, i, f, g) when not (Interval.has_zero i) -> disj (types Sup (pos, f)) (types Sup (pos, g))
      | TUntil (_, _, _, g) -> types Sup (pos, g)
      | TPrev _ -> error pos "● is never Sup"
      | _ -> Impossible (EFormula (pos, None, f, t))
    end
  | Obs -> Possible CTT
  | _ -> Impossible (EFormula (pos, None, f, t))

let rec types_transparent itvls stricts s pols (t: EnfType.t) ((pos, f): (Lexing.position * Tformula.t)): verdict =
  let error_tr pos s = Impossible (EFormulaTransparent (pos, Some s, f, t)) in
  let error pos s = Impossible (EFormula (pos, Some s, f, t)) in
  let types_transparent = types_transparent itvls stricts s pols in
  let srp = strictly_relative_past ~itl_itvs_and_strict:(itvls, stricts) in
  let types_predicate = types_predicate true in (* Set transparency requirement to true *)
  match t with
  | Cau -> begin
      match f with
      | TTT -> Possible CTT
      | TPredicate (e, _, _) -> types_predicate pols Cau e
      | TNeg f -> types_transparent Sup (pos, f)
      | TAnd (_, fs) -> List.fold_left (List.map (add_pos pos fs) ~f:(types_transparent Cau)) ~init:(Possible CTT) ~f:conj
      (* OR:Cau is typed analogously to AND:Sup *)
      | TOr (L, fs) when List.for_all (List.drop fs 1) ~f:srp -> types_transparent Cau (pos, List.hd_exn fs)
      | TOr (L, _) -> error_tr pos "∨:L (Cau) is only transparently enforceable when all formulas except for the left-most are SRP, but at least one of them is not SRP"
      | TOr (R, fs) when List.for_all (List.drop_last_exn fs) ~f:srp -> types_transparent Cau (pos, List.last_exn fs)
      | TOr (R, _) -> error_tr pos "∨:R (Cau) is only transparently enforceable when all formulas except for the right-most are SRP, but at least one of them is not SRP"
      | TOr (_, fs) ->
        let are_others_srp = Util.lists_with_one_removed fs |> List.map ~f:(List.for_all ~f:srp) in
        let is_srp_to_verdict (pos, f) = function
          | true -> Possible CTT
          | false ->
            let msg = Printf.sprintf "∨ (Cau) is transparently enforceable when all formulas besides the one used for enforcement (%s) are SRP, but at least one of them is not SRP" (Tformula.to_string f) in
            error_tr pos msg
        in
        let types_and_srp f srp = conj (types_transparent Cau f) (is_srp_to_verdict f srp) in
        List.fold_left (List.map2_exn (add_pos pos fs) are_others_srp ~f:types_and_srp) ~init:(Possible CTT) ~f:disj
      (* (a IMP b):Cau <==> (not a OR b):Cau -> thus IMP:Cau is typed analogously to AND:Sup *)
      | TImp (L, f, g) when srp g -> types_transparent Sup (pos, f)
      | TImp (L, _, _) -> error_tr pos "→:L (Cau) is only transparently enforceable when the RHS is SRP"
      | TImp (R, f, g) when srp f -> types_transparent Cau (pos, g)
      | TImp (R, _, _) -> error_tr pos "→:R (Cau) is only transparently enforceable when the LHS is SRP"
      | TImp (_, f, g) ->
        let srp_of_other_side other =
          if srp other then Possible CTT else
            let msg = Printf.sprintf "→ (Cau) is only transparently enforceable when the side not used for enforcement (%s) is SRP" (Tformula.to_string other) in
            error_tr pos msg
        in
        disj (conj (types_transparent Sup (pos, f)) (srp_of_other_side g)) (conj (types_transparent Cau (pos, g)) (srp_of_other_side f))
      (* (a IFF b):Cau <==> ((a IMP b) AND (b IMP a)):Cau -> thus IFF is typed analogously to AND:Cau and IMP:Cau *)
      | TIff (L, L, f, g) when srp g -> conj (types_transparent Sup (pos, f)) (types_transparent Cau (pos, f))
      | TIff (L, L, _, _) -> error_tr pos "↔:L,L (Cau) is only transparently enforceable when the RHS is SRP" 
      | TIff (L, R, f, g) when (srp f && srp g) -> conj (types_transparent Sup (pos, f)) (types_transparent Sup (pos, g)) (* TODO: would a Possible verdict for types_transparent already imply SRP? *)
      | TIff (L, R, f, _) when (srp f) -> error_tr pos "↔:L,R (Cau) is only transparently enforceable when both sides are SRP, but the RHS is not SRP"
      | TIff (L, R, _, g) when (srp g) -> error_tr pos "↔:L,R (Cau) is only transparently enforceable when both sides are SRP, but the LHS is not SRP" 
      | TIff (L, R, _, _) -> error_tr pos "↔:L,R (Cau) is only transparently enforceable when both sides are SRP, but neither side is SRP"
      | TIff (R, L, f, g) when (srp f && srp g) -> conj (types_transparent Cau (pos, g)) (types_transparent Cau (pos, f)) (* TODO: would a Possible verdict for types_transparent already imply SRP? *)
      | TIff (R, L, f, _) when (srp f) -> error_tr pos "f ↔:R,L g (Cau) requires that f and g are SRP, but g is not"
      | TIff (R, L, _, g) when (srp g) -> error_tr pos "f ↔:R,L g (Cau) requires that f and g are SRP, but f is not"
      | TIff (R, L, _, _) -> error_tr pos "f ↔:R,L g (Cau) requires that f and g are SRP, but neither is SRP"
      | TIff (R, R, f, g) when srp f -> conj (types_transparent Cau (pos, g)) (types_transparent Sup (pos, g))
      | TIff (R, R, _, _) -> error_tr pos "↔:R,R (Cau) LHS is not SRP"
      | TIff (_, _, f, g) ->
        let verdict_tr_f = if srp f then Possible CTT else error_tr pos "↔ (Cau) LHS is not SRP" in
        let verdict_tr_g = if srp g then Possible CTT else error_tr pos "↔ (Cau) RHS is not SRP" in
        conj
          (disj (conj (types_transparent Sup (pos, f)) verdict_tr_g) (conj (types_transparent Cau (pos, g)) verdict_tr_f))
          (disj (conj (types_transparent Cau (pos, f)) verdict_tr_g) (conj (types_transparent Sup (pos, g)) verdict_tr_f))
      (* Exists follows the same rule as the non-transparent case *)
      | TExists (_, f) -> types_transparent Cau (pos, f)
      (* Forall follows the same rule(s) as the non-transparent case *)
      | TForall (x, f) when is_past_guarded s x false f -> types_transparent Cau (pos, f)
      | TForall (x, _) -> error pos ("for causability " ^ x ^ " must be past-guarded")
      (* Next follows the same rule(s) as the non-transparent case *)
      | TNext (i, f) when Interval.equal i Interval.full -> types_transparent Cau (pos, f)
      | TNext _ -> error pos "○ with non-[0,∞) interval is never Cau"
      | TSince (_, i, f, g) when Interval.has_zero i && srp f && srp g -> types_transparent Cau (pos, g)
      | TSince (_, i, f, _) when Interval.has_zero i && srp f -> error_tr pos "f S[a,b) g requires that f and g are SRP, but g is not"
      | TSince (_, i, _, g) when Interval.has_zero i && srp g -> error_tr pos "f S[a,b) g requires that f and g are SRP, but f is not"
      | TSince (_, i, _, _) when Interval.has_zero i -> error_tr pos "f S[a,b) g requires that f and g are SRP, but neither is SRP"
      | TOnce (i, g) when Interval.has_zero i && srp g -> types_transparent Cau (pos, g)
      | TOnce (i, _) when Interval.has_zero i -> error_tr pos "⧫[a,b) g is only transparently enforceable when g is SRP"
      | TOnce _ | TSince _ -> error pos "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      (* Eventually:Cau and Always:Cau should be unaffected by the transparency requirements *)
      | TEventually (_, f) | TAlways (_, f) -> types_transparent Cau (pos, f)
      (* Until:LR (Cau) stays the same *)
      | TUntil (_, U _, _, _) -> error_tr pos "U[a,b):LR is only transparently enforceable when b≠∞"
      | TUntil (LR, _, f, g) -> conj (types_transparent Cau (pos, f)) (types_transparent Cau (pos, g))
      | TUntil (_, i, f, g) when Interval.has_zero i && srp f -> types_transparent Cau (pos, g)
      | TUntil (R, i, _, _) when Interval.has_zero i -> error_tr pos "f U[a,b):R g requires that f is SRP"
      | TUntil (_, _, f, g) -> conj (types_transparent Cau (pos, f)) (types_transparent Cau (pos, g))
      | TPrev _ -> error pos "● is never Cau"
      | _ -> Impossible (EFormula (pos, None, f, t))
    end
  | Sup -> 
    begin
      match f with
      | TFF -> Possible CTT
      | TPredicate (e, _, _) -> types_predicate pols Sup e
      | TNeg f -> types_transparent Cau (pos, f)
      | TAnd (L, fs) when List.for_all (List.drop fs 1) ~f:srp -> types_transparent Sup (pos, List.hd_exn fs)
      | TAnd (L, _) -> error_tr pos "∧:L (f::fs) (Sup) is only transparently enforceable when all formulas fs are SRP, but at least one of them is not"
      | TAnd (R, fs) when List.for_all (List.drop_last_exn fs) ~f:srp -> types_transparent Sup (pos, List.last_exn fs)
      | TAnd (R, _) -> error_tr pos "∧:R [f1,...,fn-1,fn] (Sup) requires that all formulas [f1,...,fn-1] are SRP, but at least one of them is not"
      | TAnd (_, fs) ->
        let are_others_srp = Util.lists_with_one_removed fs |> List.map ~f:(List.for_all ~f:srp) in
        let is_srp_to_verdict (pos, f) = function
          | true -> Possible CTT
          | false ->
            let msg = Printf.sprintf "∧ [f0,...,fn] (Sup) requires all formulas besides the one used for enforcement (%s) are SRP, but at least one of them is not" (Tformula.to_string f)
            in
            error_tr pos msg
        in
        let types_and_srp f is_srp = conj (types_transparent Sup f) (is_srp_to_verdict f is_srp) in
        List.fold_left (List.map2_exn (add_pos pos fs) are_others_srp ~f:types_and_srp) ~init:(Possible CTT) ~f:disj
      | TOr (_, fs) -> List.fold_left (List.map (add_pos pos fs) ~f:(types_transparent Cau)) ~init:(Possible CTT) ~f:conj
      | TImp (_, f, g) -> conj (types_transparent Cau (pos, f)) (types_transparent Sup (pos, g))
      | TIff (L, _, f, g) when srp f && srp g -> conj (types_transparent Cau (pos, f)) (types_transparent Sup (pos, g)) (* TODO: would a Possible verdict for types_transparent already imply SRP? *)
      | TIff (L, _, f, _) when (srp f) -> error_tr pos "f ↔:L,_ g (Sup) requires both f and g to be SRP, but the g is not" 
      | TIff (L, _, _, g) when (srp g) -> error_tr pos "f ↔:L,_ g (Sup) requires both f and g to be SRP, but the f is not" 
      | TIff (L, _, _, _) -> error_tr pos "f ↔:L,_ g (Sup) requires f and g to be SRP, but neither is SRP"
      | TIff (R, _, f, g) when srp f && srp g -> conj (types_transparent Sup (pos, f)) (types_transparent Cau (pos, g)) (* TODO: would a Possible verdict for types_transparent already imply SRP? *)
      | TIff (R, _, f, _) when (srp f) -> error_tr pos "f ↔:R,_ g (Sup) requires both f and g to be SRP, but g is not"
      | TIff (R, _, _, g) when (srp g) -> error_tr pos "f ↔:R,_ g (Sup) requires both f and g to be SRP, but f is not"
      | TIff (R, _, _, _) -> error_tr pos "f ↔:R,_ g (Sup) requires both f and g to be SRP, but neither is SRP"
      | TIff (_, _, f, g) ->
        let verdict_tr_f = if srp f then Possible CTT else error_tr pos "↔ (Cau) LHS is not SRP" in
        let verdict_tr_g = if srp g then Possible CTT else error_tr pos "↔ (Cau) RHS is not SRP" in
        disj
          (conj (conj (types_transparent Cau (pos, f)) verdict_tr_g) (conj (types_transparent Sup (pos, g)) verdict_tr_f))
          (conj (conj (types_transparent Sup (pos, f)) verdict_tr_g) (conj (types_transparent Cau (pos, g)) verdict_tr_f))
      | TExists (x, f) when is_past_guarded s x true f -> types_transparent Sup (pos, f)
      | TExists (x, _) -> error pos ("for suppressability " ^ x ^ " must be past-guarded")
      | TForall (_, f) -> types_transparent Sup (pos, f)
      | TNext (_, f) -> types_transparent Sup (pos, f)
      | THistorically (i, f) when Interval.has_zero i && srp f -> types_transparent Sup (pos, f)
      | THistorically (i, _) when Interval.has_zero i -> error_tr pos "■[a,b) f (Sup) requires f to be SRP"
      | THistorically _ -> error pos "■[a,b) with a > 0 is never Sup"
      | TSince (_, i, f, g) when not (Interval.has_zero i) && srp f && srp g -> types_transparent Sup (pos, f)
      | TSince (_, _, f, g) when srp f && srp g -> conj (types_transparent Sup (pos, f)) (types_transparent Sup (pos, g))
      | TSince (_, _, f, _) when srp f -> error_tr pos "f S[a,b) g (Sup) requires both f and g to be SRP, but g is not"
      | TSince (_, _, _, g) when srp g -> error_tr pos "f S[a,b) g (Sup) requires both f and g to be SRP, but f is not"
      | TSince (_, _, _, _) -> error_tr pos "f S[a,b) g (Sup) requires both f and g to be SRP, but both are not"
      | TEventually (_, f) when srp f -> types_transparent Sup (pos, f)
      | TEventually (_, _) -> error_tr pos "◇f (Sup) requires f to be SRP"
      | TAlways (B _, f) -> types_transparent Sup (pos, f)
      | TAlways _ -> error_tr pos "□[a,b) f (Sup) requires b≠∞"
      | TUntil (_, _, f, g) when srp f -> types_transparent Sup (pos, g)
      | TUntil (_, _, _, _) -> error_tr pos "f U[a,b) g (Sup) requires f to be SRP"
      | TPrev _ -> error pos "● is never Sup"
      | _ -> Impossible (EFormula (pos, None, f, t))
    end
  | Obs -> Possible CTT
  | _ -> Impossible (EFormula (pos, None, f, t))

(* todo [FH]: Extend to set ids *)
let rec convert s (pols: ('a, 'b, 'c) Base.Map.t) b enftype (form: Tformula.t) : Eformula.t option =
  let convert = convert s pols b in
  let default_L (s: Side.t) = if Side.equal s R then Side.R else L in
  let set_b = function
    | Interval.U a -> Interval.B (a, b)
    | B _ as i -> i in
  let f =
    match enftype with
      Cau -> begin
        match form with
        | Tformula.TTT -> Some (Eformula.ETT)
        | TPredicate (e, t, et) when EnfType.equal (Map.find_exn pols e) Cau -> Some (Eformula.EPredicate (e, t, et))
        | TNeg f -> (convert Sup f) >>| (fun f' -> Eformula.ENeg f')
        | TAnd (s, fs) ->
           Option.all (List.map fs ~f:(convert Cau))
           >>| (fun fs' -> Eformula.EAnd (default_L s, fs'))
        | TOr (L, f :: fs) ->
           (convert Cau f)
           >>| (fun f' -> Eformula.EOr (L, f' :: (Eformula.of_tformulas s.tevents fs)))
        | TOr (R, fs) ->
           let f, fs = List.last_exn fs, List.drop_last_exn fs in
           (convert Cau f) >>| (fun f' -> Eformula.EOr(R, (Eformula.of_tformulas s.tevents fs) @ [f']))
        | TOr (_, fs) ->
           begin
             match convert Cau (List.hd_exn fs) with
             | Some f' -> Some (Eformula.EOr (L, f' :: (Eformula.of_tformulas s.tevents fs)))
             | None    ->
                let f, fs = List.last_exn fs, List.drop_last_exn fs in
                (convert Cau f) >>| (fun f' -> Eformula.EOr (R, (Eformula.of_tformulas s.tevents  fs) @ [f']))
           end
        | TImp (L, f, g) -> (convert Sup f) >>| (fun f' -> Eformula.EImp(L, f', Eformula.of_tformula s.tevents  g))
        | TImp (R, f, g) -> (convert Cau g) >>| (fun g' -> Eformula.EImp(R, Eformula.of_tformula s.tevents  f, g'))
        | TImp (_, f, g) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Eformula.EImp (L, f', Eformula.of_tformula s.tevents  g))
             | None    -> (convert Cau g) >>| (fun g' -> Eformula.EImp (R, Eformula.of_tformula s.tevents f, g'))
           end
        | TIff (L, L, f, g) -> (convert Sup f) >>| (fun f' -> Eformula.EIff (L, L, f', Eformula.of_tformula s.tevents g))
        | TIff (L, R, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                              >>| (fun g' -> Eformula.EIff (L, R, f', g')))
        | TIff (R, L, f, g) -> (convert Cau g) >>= (fun g' -> (convert Cau f)
                                                              >>| (fun f' -> Eformula.EIff (R, L, f', g')))
        | TIff (R, R, f, g) -> (convert Cau g) >>| (fun g' -> Eformula.EIff (R, R, Eformula.of_tformula s.tevents f, g'))
        | TIff (_, _, f, g) ->
           begin
             match convert Sup f with
             | Some f' ->
                begin
                  match convert Cau f with
                  | Some f' -> Some (Eformula.EIff (L, L, f', Eformula.of_tformula s.tevents g))
                  | None    -> (convert Sup g) >>| (fun g' -> Eformula.EIff (L, R, f', g'))
                end
             | None -> (convert Cau g)
                       >>= (fun g' ->
                 match convert Cau f with
                 | Some f' -> Some (Eformula.EIff (R, L, f', g'))
                 | None    -> (convert Sup g) >>| (fun g' -> Eformula.EIff (R, R, Eformula.of_tformula s.tevents f, g')))
           end
        | TExists (x, f) -> (convert Cau f) >>| (fun f' -> Eformula.EExists (x, f'))
        | TForall (x, f) when is_past_guarded s x false f -> (convert Cau f) >>| (fun f' -> Eformula.EForall (x, f'))
        | TNext (i, f) when Interval.equal i Interval.full ->
           (convert Cau f) >>| (fun f' -> Eformula.ENext (i, f'))
        | TOnce (i, f) when Interval.has_zero i ->
           (convert Cau f) >>| (fun f' -> Eformula.EOnce (i, f'))
        | TSince (_, i, f, g) when Interval.has_zero i ->
           (convert Cau g) >>| (fun g' -> Eformula.ESince (R, i, Eformula.of_tformula s.tevents f, g'))
        | TEventually (i, f) -> (convert Cau f) >>| (fun f' -> Eformula.EEventually (set_b i, Interval.is_bounded i, f'))
        | TAlways (i, f) -> (convert Cau f) >>| (fun f' -> Eformula.EAlways (i, true, f'))
        | TUntil (LR, i, f, g) ->
           (convert Cau f) >>= (fun f' -> (convert Cau g) >>| (fun g' -> Eformula.EUntil (LR, set_b i, Interval.is_bounded i, f', g')))
        | TUntil (_, i, f, g) when Interval.has_zero i ->
           (convert Cau g) >>| (fun g' -> Eformula.EUntil (LR, set_b i, Interval.is_bounded i, Eformula.of_tformula s.tevents f, g'))
        | TUntil (L, i, f, g) ->
           (convert Cau g) >>| (fun g' -> Eformula.EUntil (LR, set_b i, Interval.is_bounded i, Eformula.of_tformula s.tevents f, g'))
        | _ -> None
      end
    | Sup -> begin
        match form with
        | TFF -> Some (Eformula.EFF)
        | TPredicate (e, t, et) when EnfType.equal (Map.find_exn pols e) Sup -> Some (Eformula.EPredicate (e, t, et))
        | TNeg f -> (convert Cau f) >>| (fun f' -> Eformula.ENeg f')
        | TAnd (L, f :: fs) -> (convert Sup f) >>| (fun f' -> Eformula.EAnd (L, f' :: (Eformula.of_tformulas s.tevents fs)))
        | TAnd (R, fs) ->
           let f, fs = List.last_exn fs, List.drop_last_exn fs in
           (convert Sup f) >>| (fun f' -> Eformula.EAnd (R, (Eformula.of_tformulas s.tevents fs) @ [f']))
        | TAnd (_, fs) ->
           begin
              match convert Sup (List.hd_exn fs) with
             | Some f' -> Some (Eformula.EAnd (L, f' :: (Eformula.of_tformulas s.tevents (List.tl_exn fs))))
             | None    ->
                let f, fs = List.last_exn fs, List.drop_last_exn fs in
                (convert Sup f) >>| (fun f' -> Eformula.EAnd (R, (Eformula.of_tformulas s.tevents fs) @ [f']))
           end
        | TOr (s, fs) ->
           Option.all (List.map fs ~f:(convert Sup))
           >>| (fun fs' -> Eformula.EOr (default_L s, fs'))
        | TImp (s, f, g) -> (convert Cau f) >>= (fun f' -> (convert Sup g)
                                                          >>| (fun g' -> Eformula.EImp (default_L s, f', g')))
        | TIff (L, _, f, g) -> (convert Cau f) >>= (fun f' -> (convert Sup g)
                                                             >>| (fun g' -> Eformula.EIff (L, N, f', g')))
        | TIff (R, _, f, g) -> (convert Sup f) >>= (fun f' -> (convert Cau g)
                                                             >>| (fun g' -> Eformula.EIff (R, N, f', g')))
        | TIff (_, _, f, g) ->
           begin
             match convert Cau f, convert Sup g with
             | Some f', Some g' -> Some (Eformula.EIff (L, R, f', g'))
             | _, _ -> match convert Sup f, convert Cau g with
                       | Some f', Some g' -> Some (Eformula.EIff(R, L, f', g'))
                       | _, _ -> None
           end
        | TExists (x, f) when is_past_guarded s x true f ->
           (convert Sup f) >>| (fun f' -> Eformula.EExists (x, f'))
        | TForall (x, f) ->  (convert Sup f) >>| (fun f' -> Eformula.EForall (x, f'))
        | TNext (i, f) -> (convert Sup f) >>= (fun f' -> Some (Eformula.ENext (i, f')))
        | THistorically (i, f) when Interval.has_zero i ->
           (convert Sup f) >>| (fun f' -> Eformula.EHistorically (i, f'))
        | TSince (_, i, f, g) when not (Interval.has_zero i) ->
           (convert Sup f) >>| (fun f' -> Eformula.ESince (L, i, f', Eformula.of_tformula s.tevents g))
        | TSince (_, i, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                                    >>| (fun g' -> Eformula.ESince (LR, i, f', g')))
        | TEventually (i, f) -> (convert Sup f) >>| (fun f' -> Eformula.EEventually (i, true, f'))
        | TAlways (i, f) -> (convert Sup f) >>| (fun f' -> Eformula.EAlways (set_b i, Interval.is_bounded i, f'))
        | TUntil (L, i, f, g) when not (Interval.has_zero i) ->
           (convert Sup f) >>| (fun f' -> Eformula.EUntil (L, i, true, f', Eformula.of_tformula s.tevents g))
        | TUntil (R, i, f, g) when not (Interval.has_zero i) ->
           (convert Sup g) >>| (fun g' -> Eformula.EUntil (R, i, true, Eformula.of_tformula s.tevents f, g'))
        | TUntil (_, i, f, g) when not (Interval.has_zero i) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Eformula.EUntil (L, i, true, f', Eformula.of_tformula s.tevents g))
             | None -> (convert Sup g) >>| (fun g' -> Eformula.EUntil (R, i, true, Eformula.of_tformula s.tevents f, g'))
           end
        | TUntil (_, i, f, g) -> (convert Sup g) >>| (fun g' -> Eformula.EUntil (R, i, true, Eformula.of_tformula s.tevents f, g'))
        | _ -> None
      end
    | Obs -> Some (Eformula.of_tformula s.tevents form).f
    | _ -> assert false
  in
  (*Stdio.print_string (EnfType.to_string enftype ^ " " ^ Formula.to_string form ^ " -> ");*)
  match f with Some f -> Some Eformula.{ f; enftype; id = 0 } | None -> None

let convert_enforceable s pols (f: Tformula.t) b pos =
  if not (Set.is_empty (Tformula.fv f)) then
    let err_msg =
      Printf.sprintf "formula %s is not closed" (Tformula.to_string f) in
    Util.enf_error err_msg (Some pos)
  else ();
  match types s pols Cau (pos, f) with (* TODO: check if policy constraints are necessary (and how to get them) *)
  | Possible c ->
     begin
       match Constraints.solve c with
       | sol::_ ->
          begin
            (*Map.iteri sol ~f:(fun ~key ~data -> Pred.Sig.update_enftype key data);*)
            ignore sol; (* todo [FH]: check consistency of solutions over formulae *)
            let pols' = Map.map pols ~f:fst in
            match convert s pols' b Cau f with
              Some f' -> f'
            | None    -> let err_msg = Printf.sprintf "formula\n %s\ncannot be converted" (Tformula.to_string f) in
                         Util.enf_error err_msg (Some pos)
          end
       | _ -> let err_msg = Printf.sprintf "formula\n %s\n is not enforceable becuase the constraint\n %s\nhas no solution"
                              (Tformula.to_string f) (Constraints.to_string c) in
              Util.enf_error err_msg (Some pos)
     end
  | Impossible e ->
     let err_msg = Printf.sprintf "The formula\n %s\nis not enforceable. To make it enforceable, you would need to\n %s"
                     (Tformula.to_string f) (Errors.to_string e) in
     Util.enf_error err_msg (Some pos)

(* let convert_transparently_enforceable s pols (f: Tformula.t) b pos =
  let f' = convert_enforceable s pols f b pos in
  if is_transparent f' then
    f'
  else
    let err_msg = Printf.sprintf "The formula\n %s\nis not transparently enforceable."
                     (Tformula.to_string f) in
    Util.enf_error err_msg (Some pos) *)

let epattern_of_tpattern s = function
  | TPPresent -> EPPresent
  | TPEventually i -> EPEventually i
  | TPAlways i -> EPAlways i
  | TPUntil (i, f) -> EPUntil (i, Eformula.of_tformula s.tevents f)
  | TPOnce i -> EPOnce i
  | TPHistorically i -> EPHistorically i
  | TPSince (i, f) -> EPSince (i, Eformula.of_tformula s.tevents f)

let type_tsrule erule_map =
  function
  | TSRule (pos, idx, label, type_fixes, _, doc_string) -> begin
      let rule = Map.find_exn erule_map idx in
      ESRule (pos, idx, label, type_fixes, rule, doc_string)
    end
  | _ -> assert false

let type_tstmt erule_map = function
  | TSImport (pos, idents, import_format) ->
     ESImport (pos, idents, import_format)
  | TSSection (section_kind, full_label, label, title) -> 
     ESSection (section_kind, full_label, label, title)
  | TSRule _ as trule -> type_tsrule erule_map trule
  | TSEvent (event_type, name, typed_args, pol, doc_string) ->
     ESEvent (event_type, name, typed_args, pol, doc_string)
  | TSType (name, typ, doc_string) -> ESType (name, typ, doc_string)
  | TSFunction (name, arg_types, return_type, doc_string) ->
     ESFunction (name, arg_types, return_type, doc_string)
  | TSNote text -> ESNote text

let type_exception s f = Eformula.of_tformula s.tevents f

let type_scope s f = Eformula.of_tformula s.tevents f

let def_sets (rules: (int, trule_compilation, 'a) Map.t) (events: (string, tevent, 'b) Map.t) : (int, string list, 'a) Map.t =
  let aux = function
    | TCImplication _ -> []
    | TCDefinition (_, _, _, _, _, _, _, _, Tformula.TPredicate (name, _, _)) -> [name]
    | TCDefinition _ -> assert false
    | TCDefinitionDis (disjuncts, Tformula.TPredicate (name, _, _)) ->
      let positions = Map.map disjuncts ~f:(fun (_, _, pos, _, _, _, _, _) -> pos) |> Map.data in
      (match Map.find events name with
        | Some (_, _, Lex.TItl, _) -> ()
        | Some (_, _, pol, _) ->
          let err_msg = Printf.sprintf "Can only constitute 'Internal' events, but \"%s\" is \"%s\"\nat locations:\n%s" name (Lex.string_of_pol pol) (List.map positions ~f:Util.string_of_pos |> Util.string_of_string_list_new_line) in
          Util.enf_error err_msg None
        | None -> (* TODO: is this even possible, i.e. could/should this be an `assert false` instead? *)
          let err_msg = Printf.sprintf "Unknown event \"%s\"\nat locations:\n%s" name (List.map positions ~f:Util.string_of_pos |> Util.string_of_string_list_new_line) in
          Util.enf_error err_msg None
      );
      [name]
    | TCDefinitionDis _ -> assert false
  in
  Map.map rules ~f:aux

let use_sets (rules: (int, trule_compilation, Int.comparator_witness) Map.t) (events: (string, tevent, Base.String.comparator_witness) Map.t) : (int, string list, 'a) Map.t =
  let use_formula = function
    | TPredicate (name, _, _) -> (match Map.find events name with
      | Some (_, _, Lex.TItl, _) -> [name]
      | _ -> [])
    | _ -> []
  in
  let use_formulas f = List.concat_map f ~f:use_formula in
  let use_pattern = function
    | TPPresent
    | TPEventually _
    | TPAlways _
    | TPOnce _
    | TPHistorically _ -> []
    | TPUntil (_, f)
    | TPSince (_, f) -> use_formula f
  in
  let use_disjunct (_, _, _, f, p, exceptions, scopes, term_conditions) = ((List.map ~f:snd (f@exceptions@scopes) @ term_conditions) |> use_formulas) @ use_pattern p in
  let use_disjuncts disjuncts = Map.map disjuncts ~f:use_disjunct |> Map.data |> List.concat in
  let snd_map l = List.map l ~f:snd in
  let aux = function
    | TCImplication (_, _, _, f1, p, exceptions, scopes, f2, q, _, _) ->
      use_formulas (snd_map (f1@exceptions@scopes)) @ use_pattern p @ use_formulas (snd_map f2) @ use_pattern q |> List.dedup_and_sort ~compare:String.compare
    | TCDefinition (_, _, _, f1, p, exceptions, scopes, _, _) ->
      use_formulas (snd_map (f1@exceptions@scopes)) @ use_pattern p |> List.dedup_and_sort ~compare:String.compare
    | TCDefinitionDis (disjuncts, _) ->
      use_disjuncts disjuncts |> List.dedup_and_sort ~compare:String.compare
  in
  Map.map rules ~f:aux

let collect_rule_indices (tprog: Tlex.tprog) =
  let aux l stmt =
    match stmt with
    | TSRule (_, idx, _, _, _, _) -> idx::l
    | _ -> l
  in
  List.fold tprog.tstmts ~f:aux ~init:[]

let topological_sort (rule_indices: int list) (def: (int, string list, 'a) Map.t) (use: (int, string list, 'a) Map.t) : int list =
  let def_inv = Util.invert_int_string_multimap def in
  let init, rest = List.partition_tf rule_indices ~f:(fun r -> not (Map.mem use r)) in (*all rules that do not 'use' any internal events*)
  let rec aux visited rest =
    match rest with
      | [] -> visited
      | _ ->
        let partition_function r1 =
          let condition_for_used_event e =
            let rules_defining_e = Map.find_multi def_inv e in
            let condition_for_rule_defining_e r2 =
              List.mem visited r2 ~equal:Int.equal
            in
            List.for_all rules_defining_e ~f:condition_for_rule_defining_e
          in
          let used_events_in_r1 = Map.find_multi use r1 in
          List.for_all used_events_in_r1 ~f:condition_for_used_event (* If all event used by rule r1 have been defined by rules already visited, then we can add r1 to the visited rules *)
        in
        let fully_defined, rest = List.partition_tf rest ~f:partition_function in
        begin match fully_defined with
        (* TODO: improve this error reporting, maybe report the actual cycle *)
        | [] -> Util.enf_error "Circular dependency of internal events" None
        | _ -> ()
        end;
        aux (visited @ fully_defined) rest
    in
  aux init rest |> List.rev

let type_pattern_with_formulas itl_srp (s:Tlex.tprog) (pos:Lexing.position) pols enftype fs (p: Tlex.tpattern) : verdict =
  let types = match itl_srp with
    | Some (itvs, stricts) -> types_transparent itvs stricts
    | None -> types
  in
  let type_for_all_formulas fs t =
    List.map fs ~f:(types s pols t)
    |> List.fold ~f:conj ~init:(Possible CTT)
  in
  let type_for_at_least_one_formula fs t = match itl_srp with
    | Some (itvls, stricts) -> (* transparency requires that other formulas are SRP *)
      let fs' = List.map fs ~f:snd in
      let srp = strictly_relative_past ~itl_itvs_and_strict:(itvls, stricts) in
      let are_others_srp = Util.lists_with_one_removed fs' |> List.map ~f:(List.for_all ~f:srp) in
      let is_srp_to_verdict (pos, f) = function
        | true -> Possible CTT
        | false ->
          let msg = Printf.sprintf "the conjunction of exception predicates is transparently enforceable when all predicates besides the one used for enforcement (%s) are SRP, but at least one of them is not SRP" (Tformula.to_string f) in
          Impossible (EFormulasTransparent (pos, Some ("AND", msg), fs', t))
      in
      let types_and_srp f srp = conj (types s pols t f) (is_srp_to_verdict f srp) in
      List.fold_left (List.map2_exn fs are_others_srp ~f:types_and_srp) ~init:(Possible CTT) ~f:disj
    | None ->
      let init =
        let msg =  "none of the provided formulas can be made Sup" in
        Impossible (EPattern (pos, msg, p, fs, enftype))
      in
      List.map fs ~f:(types s pols t) |> List.fold ~f:disj ~init:init
  in
  match enftype with
  | Cau ->
    begin match p with
    | TPPresent -> type_for_all_formulas fs Cau
    | TPEventually _ -> type_for_all_formulas fs Cau
    | TPAlways _ -> type_for_all_formulas fs Cau
    | TPUntil (i, _) when Interval.is_bounded i -> type_for_all_formulas fs Cau
    | TPUntil _ -> Impossible (EPattern (pos, "can only be made \"Cau\" if the interval is bounded", p, fs, enftype))
    | TPOnce i when Interval.has_zero i -> type_for_all_formulas fs Cau
    | TPOnce _ -> Impossible (EPattern (pos, "can only be made \"Cau\" if zero is in the interval", p, fs, enftype))
    | TPHistorically _ -> Impossible (EPattern (pos, "can never be made \"Cau\"", p, fs, enftype))
    | TPSince (i, g) when Interval.has_zero i -> types s pols Cau (pos, g)
    | TPSince _ -> Impossible (EPattern (pos, "can only be made \"Cau\" if zero is in the interval", p, fs, enftype))
    end
  | Sup ->
    begin match p with
    | TPPresent -> type_for_at_least_one_formula fs Sup
    | TPEventually _ -> type_for_at_least_one_formula fs Sup
    | TPAlways _ -> type_for_at_least_one_formula fs Sup
    | TPUntil _ -> type_for_at_least_one_formula fs Sup
    | TPOnce _ -> Impossible (EPattern (pos, "can never be made \"Sup\"", p, fs, enftype))
    | TPHistorically _ -> type_for_at_least_one_formula fs Sup
    | TPSince (i, g) when Interval.has_zero i -> type_for_at_least_one_formula fs Sup |> conj (types s pols Cau (pos, g))
    | TPSince _ -> type_for_at_least_one_formula fs Sup (* when not (Interval.has_zero i) *)
    end
  | Obs -> Possible CTT
  | _ -> Impossible (EPattern (pos, "can only be made \"Cau\", \"Sup\", or \"Obs\"", p, fs, enftype))

let get_exception_predicates ?(negated=false) (s: Tlex.tprog) rule_idx =
  let exception_idxs = Map.find_multi s.rule_tree.exceptions rule_idx in
  let exception_predicates = List.map exception_idxs ~f:(try Map.find_exn s.exception_predicates with _ -> assert false) in
  let exception_predicates = if negated then List.map exception_predicates ~f:Tformula.tneg else exception_predicates in
  let exception_positions = List.map exception_idxs ~f:(fun x -> try snd (Map.find_exn s.rule_tree.label_of_rule x) with _ -> assert false) in
  List.zip_exn exception_positions exception_predicates

let get_scope_predicates (s: Tlex.tprog) rule_idx = 
  let scope_idxs = Map.find_multi s.rule_tree.scopes rule_idx in
  let scope_predicates = List.map scope_idxs ~f:(try Map.find_exn s.scope_predicates with _ -> assert false) in
  let scope_positions = List.map scope_idxs ~f:(fun x -> try snd (Map.find_exn s.rule_tree.label_of_rule x) with _ -> assert false) in
  List.zip_exn scope_positions scope_predicates

let pols_from_rule_constraints pos rcs =
  let add_policy_constraint enftype pols = function
    | Lex.CEvent id -> begin
      match Map.find pols id with
        | Some enftype' when EnfType.equal enftype enftype' ->
          let warning = Printf.sprintf "Event \"%s\" is marked as \"%s\" multiple times" id (EnfType.to_string enftype) in
          Util.warning warning (Some pos);
          pols
        | Some Cau | Some Sup ->
          let err_msg = Printf.sprintf "Cannot mark event \"%s\" as both suppressing and causing" id in
          Util.enf_error err_msg (Some pos)
        | Some _ -> assert false
        | None -> Map.add_exn pols ~key:id ~data:enftype
      end
    | _ -> pols
  in
  let aux pols = function
    | Lex.Suppressing constr_kind -> List.fold constr_kind ~f:(add_policy_constraint Sup) ~init:pols
    | Lex.Causing constr_kind -> List.fold constr_kind ~f:(add_policy_constraint Cau) ~init:pols
  in
  let make_option pols = if Map.is_empty pols then None
                         else (Some pols) in
  List.fold rcs ~f:aux ~init:(Map.empty (module String))
  |> make_option

let causing_effects pos rcs =
  let filter_effects = function
    | Lex.CEffects -> true
    | _ -> false
  in
  let aux = function
    | Lex.Causing constr_kind ->
      List.filter constr_kind ~f:filter_effects
    | Lex.Suppressing constr_kind ->
      if List.exists constr_kind ~f:filter_effects then
        let err_msg = "Cannot enforce (cause) a rule by suppressing its effects"  in
        Util.enf_error err_msg (Some pos)
      else
        []
  in
  match List.concat_map rcs ~f:aux with
    | [Lex.CEffects] -> true
    | Lex.CEffects::_ ->
      let warning = "\"causing effects\" is specified multiple times" in
      Util.warning warning (Some pos);
      true
    | [] -> false
    | _ -> assert false

let suppressing_conditions pos rcs =
  let filter_conditions = function
    | Lex.CConditions -> true
    | _ -> false
  in
  let aux = function
    | Lex.Suppressing constr_kind ->
      List.filter constr_kind ~f:filter_conditions
    | Lex.Causing constr_kind ->
      if List.exists constr_kind ~f:filter_conditions then
        let err_msg = "Cannot enforce (cause) a rule by causing its conditions"  in
        Util.enf_error err_msg (Some pos)
      else
        []
  in
  match List.concat_map rcs ~f:aux with
    | [Lex.CConditions] -> true
    | Lex.CConditions::_ ->
      let warning = "\"suppressing conditions\" is specified multiple times" in
      Util.warning warning (Some pos);
      true
    | [] -> false
    | _ -> assert false

let causing_exceptions pos rcs =
  let filter_exceptions = function
    | Lex.CExceptions -> true
    | _ -> false
  in
  let aux = function
    | Lex.Causing constr_kind ->
      List.filter constr_kind ~f:filter_exceptions
    | Lex.Suppressing constr_kind ->
      if List.exists constr_kind ~f:filter_exceptions then
        let err_msg = "Cannot enforce (cause) a rule by suppressing its exceptions"  in
        Util.enf_error err_msg (Some pos)
      else
        []
  in
  match List.concat_map rcs ~f:aux with
    | [Lex.CExceptions] -> true
    | Lex.CExceptions::_ ->
      let warning = "\"causing exceptions\" is specified multiple times" in
      Util.warning warning (Some pos);
      true
    | [] -> false
    | _ -> assert false

let suppressing_scopes pos rcs =
  let filter_scopes = function
    | Lex.CScopes -> true
    | _ -> false
  in
  let aux = function
    | Lex.Suppressing constr_kind ->
      List.filter constr_kind ~f:filter_scopes
    | Lex.Causing constr_kind ->
      if List.exists constr_kind ~f:filter_scopes then
        let err_msg = "Cannot enforce (cause) a rule by causing its scopes"  in
        Util.enf_error err_msg (Some pos)
      else
        []
  in
  match List.concat_map rcs ~f:aux with
    | [Lex.CScopes] -> true
    | Lex.CScopes::_ ->
      let warning = "\"suppressing scopes\" is specified multiple times" in
      Util.warning warning (Some pos);
      true
    | [] -> false
    | _ -> assert false

let collect_suppressing_indices pos rcs =
  let filter_indices = function
    | Lex.CCondition id -> Some id
    | _ -> None
  in
  let aux = function
    | Lex.Suppressing constr_kind ->
      List.filter_map constr_kind ~f:filter_indices
    | Lex.Causing constr_kind -> begin
      match List.filter_map constr_kind ~f:filter_indices with
        | [] -> []
        | ids ->
          let err_msg = Printf.sprintf "Cannot enforce (cause) a rule by causing a condition (conditions: \"%s\" are marked as causing)" (Util.string_of_int_list ids) in
          Util.enf_error err_msg (Some pos)
      end
  in
  let ids = List.concat_map rcs ~f:aux in
  let sorted_ids = List.dedup_and_sort ~compare:Int.compare ids in
  if List.length ids <> List.length sorted_ids then
    let warning = "Some condition(s) are marked as suppressing multiple times" in
    Util.warning warning (Some pos)
  else
    ();
  if List.is_empty sorted_ids then None
  else Some sorted_ids

let suppress_indices_are_in_range pos suppress_indices num_conditions = match suppress_indices with
  | Some indices ->
    let index_out_of_range idx = num_conditions <= idx in
    let indices_out_of_range = List.filter indices ~f:index_out_of_range in
    if not (List.is_empty indices_out_of_range) then
      let err_msg = Printf.sprintf
        "Some condition indices are out of range: %s. There are only %d conditions, indices must be strictly less than that"
          (Util.string_of_int_list indices_out_of_range)
          num_conditions
      in
      Util.enf_error err_msg (Some pos)
  | None -> ()

let update_suppress_indices_with_suppress_conditions pos suppress_indices suppress_conditions =
  if suppress_conditions && not (Option.is_some suppress_indices) then
    let warning = Printf.sprintf
      "When \"suppressing conditions\" is used, \"suppressing condition[i]\" is redundant, but conditions: %s are explicitly marked as suppressing"
        (Util.string_of_int_list (Option.value_exn suppress_indices))
    in
    Util.warning warning (Some pos);
    None
  else suppress_indices

let vanilla_rule_constraints_warning pos rcs =
  if not (List.is_empty rcs) then
    let warning = "rule constraints (\"suppressing ...\" or \"causing ...\") are ignored for rules not marked as \"(transparently) enforceable" in
    Util.warning warning (Some pos)

let combine_cause_effects_and_suppress_conditions pos cause_effects suppress_conditions =
  match cause_effects, suppress_conditions with
    | true, true ->
      let warning = "Using both \"causing effects\" and \"suppressing conditions\" is redundant" in
      Util.warning warning (Some pos);
      true, true
    | true, false -> true, false
    | false, true -> false, true
    | false, false -> true, true (* if no constraints are given, the compiler will infer how to enforce a rule during typing *)

let string_of_suppressing_or_causing = function
  | Sup -> "suppressing"
  | Cau -> "causing"
  | _ -> assert false

let check_pol_constrs pos pol_constrs pols =
  let check_pol_constr ~key:id ~data:enftype =
    match Map.find pols id with
      | Some enftype' when not (EnfType.leq enftype enftype') ->
        let err_msg = Printf.sprintf "Event \"%s\" is marked as \"%s\", but the event is defined as \"%s\"" id (string_of_suppressing_or_causing enftype) (EnfType.to_string enftype') in
        Util.enf_error err_msg (Some pos)
      | Some _ -> enftype
      | None ->
        let err_msg = Printf.sprintf "Event \"%s\" is marked as \"%s\", but the event is not defined" id (string_of_suppressing_or_causing enftype) in
        Util.enf_error err_msg (Some pos)
  in
  Map.mapi pol_constrs ~f:check_pol_constr

(* let type_exceptions ?(tr=false, (Map.empty (module String), Map.empty (module String))) s pos pols exceptions = *)
let type_exceptions itl_srp s pos pols exceptions =
  let exceptions_neg = List.map exceptions ~f:(fun (p, f) -> (p, Tformula.tneg f)) in
  type_pattern_with_formulas itl_srp s pos pols Sup exceptions_neg TPPresent

let type_scopes itl_srp s pos pols scopes =
  type_pattern_with_formulas itl_srp s pos pols Sup scopes TPPresent

(* TODO: may be used for a later version of rule-constraints *)
(* let combine_with_internal_events internal_events pols =
  Map.merge internal_events pols ~f:(fun ~key:_ -> function
    | `Right enftype -> Some enftype
    | `Left Itl -> Some Itl
    | `Left _ -> None
    | `Both (_, enftype) -> Some enftype
  ) *)

let parse_rule_constraints pos pols n rcs =
    let pol_constr = pols_from_rule_constraints pos rcs in
    let pols = match pol_constr with
      | Some pols' -> check_pol_constrs pos pols pols'
                      (* |> combine_with_internal_events pols *)
                      (* TODO: this may be used when rule-constraints for obligation rules apply transitively to internal events used in said obligation *)
      | None -> pols
    in
    let pols = Map.map pols ~f:(fun t -> (t, false)) in (* mark all events as not required to be transparent *)
    let cause_exceptions = causing_exceptions pos rcs in
    let suppress_scopes = suppressing_scopes pos rcs in
    let cause_effects = causing_effects pos rcs in
    let suppress_conditions = suppressing_conditions pos rcs in
    let suppress_indices = collect_suppressing_indices pos rcs in
    suppress_indices_are_in_range pos suppress_indices n;
    let suppress_indices = update_suppress_indices_with_suppress_conditions pos suppress_indices suppress_conditions in
    let cause_effects, suppress_conditions = combine_cause_effects_and_suppress_conditions pos cause_effects suppress_conditions in
    pols, suppress_indices, suppress_conditions, cause_effects, suppress_scopes, cause_exceptions

let update_pols_with_transparency_conditions pols pols_tr =
  Map.merge pols pols_tr ~f:(fun ~key:_ -> function
    | `Left enftype -> Some (enftype, false)
    | `Right _ -> assert false
    | `Both (enftype, (_, tr)) -> Some (enftype, tr)
  )

let strict_of_pattern_with_formulas stricts fs p =
  let strict_of_formulas itv fut fs = List.map fs ~f:snd
                              |> List.for_all ~f:(strict ~itl_strict:stricts ~itv:itv ~fut:fut)
  in
  match p with
  | TPPresent -> strict_of_formulas (Zinterval.singleton 0) false fs
  | TPEventually i
    | TPAlways i -> strict_of_formulas (Zinterval.of_interval i) true fs
  | TPOnce i
    | TPHistorically i -> strict_of_formulas (Zinterval.inv (Zinterval.of_interval i)) false fs
  | TPUntil (i, g) -> (strict_of_formulas (Zinterval.inv (Zinterval.of_interval i)) true fs)
                      || (strict ~itl_strict:stricts ~itv:(Zinterval.inv (Zinterval.of_interval i)) ~fut:true g)
  | TPSince (i, g) -> (strict_of_formulas (Zinterval.inv (Zinterval.of_interval i)) false fs)
                      || (strict ~itl_strict:stricts ~itv:(Zinterval.inv (Zinterval.of_interval i)) ~fut:false g)

let relative_interval_of_pattern_with_formulas itvls fs p =
  let j =
    let aux (_, f) = relative_interval ~itl_itvs:itvls f in
    List.fold_left (List.map fs ~f:aux) ~init:Zinterval.full ~f:Zinterval.lub
  in
  match p with
  | TPPresent -> j
  | TPEventually i
  | TPAlways i ->
    let i = Zinterval.of_interval i in
    Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
  | TPOnce i
  | TPHistorically i ->
    let i = Zinterval.of_interval i |> Zinterval.inv in
    Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
  | TPUntil (i, g) ->
    let i = Zinterval.of_interval i in
    let k = relative_interval ~itl_itvs:itvls g in
    (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i) k)
      (Zinterval.sum i j))
  | TPSince (i, g) ->
    let i = Zinterval.of_interval i in
    let k = relative_interval ~itl_itvs:itvls g in
    (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i) j)
      (Zinterval.sum i k))

let strictly_relative_past_of_pattern_with_formulas (itvls, stricts) fs p =
  (Zinterval.is_nonpositive (relative_interval_of_pattern_with_formulas itvls fs p))
  && (strict_of_pattern_with_formulas stricts fs p)

let srp_of_pattern_with_formulas (itvls, stricts) fs p =
  strictly_relative_past_of_pattern_with_formulas (itvls, stricts) fs p

let type_trule_compilation itl_itvs_and_stricts (s:Tlex.tprog) (verdict:verdict) rule =
  let pols = Tlex.pol_map s
             |> Map.map ~f:Lex.pol_to_enftype
  in
  let dnf_of_v = match verdict with
    | Possible c -> dnf c
    | Impossible e ->
      let err_msg = Printf.sprintf "Impossible: %s" (Errors.to_string e) in
      Util.enf_error err_msg None
  in
  match rule with
    | TCImplication (_, _, pos, f1, p, exceptions, scopes, f2, q, rt, rcs) ->
      begin match rt with
        | Vanilla ->
          vanilla_rule_constraints_warning pos rcs;
          verdict (* do not aadd any typing constraints in regards to this rule *)
        | Enforceable ->
          let pols, suppress_indices, suppress_conditions, cause_effects, suppress_scopes, cause_exceptions =
            parse_rule_constraints pos pols (List.length f1) rcs
          in
          let verdict_exceptions =
            if cause_exceptions then type_exceptions None s pos pols exceptions
            else Impossible (ERule (pos, "exceptions are not marked as causing"))
          in
          let verdict_scopes =
            if suppress_scopes then type_scopes None s pos pols scopes
            else Impossible (ERule (pos, "scopes are not marked as suppressing"))
          in
          let verdict_references = disj verdict_exceptions verdict_scopes in
          let verdict_conditions =
            if suppress_conditions then
              type_pattern_with_formulas None s pos pols Sup f1 p
              |> disj verdict_references
            else
              match suppress_indices with
                | Some indices ->
                  let f1_filtered = List.filteri f1 ~f:(fun i _ -> List.mem indices i ~equal:Int.equal) in
                  type_pattern_with_formulas None s pos pols Sup f1_filtered p
                | None ->
                  Impossible (ERule (pos, "no conditions are marked as suppressing"))
          in
          let verdict_effects =
            if cause_effects then type_pattern_with_formulas None s pos pols Cau f2 q
            else Impossible (ERule (pos, "effects are not marked as causing"))
          in
          let verdict_rule_implication = disj verdict_conditions verdict_effects |> conj verdict in
          begin match verdict_rule_implication with
            | Possible _ -> verdict_rule_implication
            | Impossible e ->
              let err_msg = Printf.sprintf "Impossible, rule is not enforceable: %s" (Errors.to_string e) in
              Util.enf_error err_msg (Some pos)
          end
        | Transparent ->
          let tr = Some (itl_itvs_and_stricts) in
          let pols, suppress_indices, suppress_conditions, cause_effects, suppress_scopes, cause_exceptions =
            parse_rule_constraints pos pols (List.length f1) rcs
          in
          let srp = strictly_relative_past ~itl_itvs_and_strict:itl_itvs_and_stricts in
          let srp_exceptions = List.for_all exceptions ~f:(fun (_, f) -> srp f) in
          let srp_scopes = List.for_all scopes ~f:(fun (_, f) -> srp f) in
          let srp_conditions = srp_of_pattern_with_formulas itl_itvs_and_stricts f1 p in
          let srp_effects = srp_of_pattern_with_formulas itl_itvs_and_stricts f2 p in
          let verdict_exceptions =
            if cause_exceptions then
              if srp_scopes && srp_conditions && srp_effects then
                type_exceptions None s pos pols exceptions
              else
                let not_srp = match srp_scopes, srp_conditions, srp_effects with
                  (* TODO: maybe write a function to simplify the construction of such strings *)
                  | true, true, true -> assert false
                  | false, true, true -> "scopes"
                  | true, false, true -> "conditions"
                  | true, true, false -> "effects"
                  | false, false, true -> "scopes and conditions"
                  | false, true, false -> "scopes and effects"
                  | true, false, false -> "conditions and effects"
                  | false, false, false -> "scopes, conditions, and effects"
                in
                Impossible (ERule (pos, "can't make exceptions Cau, because " ^ not_srp ^ " are not SRP"))
            else Impossible (ERule (pos, "exceptions are not marked as causing"))
          in
          let verdict_scopes =
            if suppress_scopes then
              if srp_exceptions && srp_conditions && srp_effects then
                type_scopes None s pos pols scopes
              else
                let not_srp = match srp_exceptions, srp_conditions, srp_effects with
                  (* TODO: maybe write a function to simplify the construction of such strings *)
                  | true, true, true -> assert false
                  | false, true, true -> "exceptions"
                  | true, false, true -> "conditions"
                  | true, true, false -> "effects"
                  | false, false, true -> "exceptions and conditions"
                  | false, true, false -> "exceptions and effects"
                  | true, false, false -> "conditions and effects"
                  | false, false, false -> "exceptions, conditions, and effects"
                in
                Impossible (ERule (pos, "can't make scopes Sup, because " ^ not_srp ^ " are not SRP"))
            else Impossible (ERule (pos, "scopes are not marked as suppressing"))
          in
          let verdict_references = disj verdict_exceptions verdict_scopes in
          let verdict_conditions =
            if suppress_conditions then
              if srp_exceptions && srp_scopes && srp_effects then
                type_pattern_with_formulas tr s pos pols Sup f1 p
                |> disj verdict_references
              else
                let not_srp = match srp_exceptions, srp_scopes, srp_effects with
                  (* TODO: maybe write a function to simplify the construction of such strings *)
                  | true, true, true -> assert false
                  | false, true, true -> "exceptions"
                  | true, false, true -> "scopes"
                  | true, true, false -> "effects"
                  | false, false, true -> "exceptions and scopes"
                  | false, true, false -> "exceptions and effects"
                  | true, false, false -> "scopes and effects"
                  | false, false, false -> "exceptions, scopes, and effects"
                in
                Impossible (ERule (pos, "can't make conditions Sup, because " ^ not_srp ^ " are not SRP"))
            else
              match suppress_indices with
                | Some indices ->
                  let used = List.filteri f1 ~f:(fun i _ -> List.mem indices i ~equal:Int.equal) in
                  let unused = List.filteri f1 ~f:(fun i _ -> List.mem indices i ~equal:(fun x y -> Int.equal x y |> not)) in
                  let srp_conditions_unused = srp_of_pattern_with_formulas itl_itvs_and_stricts unused p in
                  if srp_conditions_unused && srp_exceptions && srp_scopes && srp_effects then
                    type_pattern_with_formulas tr s pos pols Sup used p
                  else
                    let not_srp = match srp_conditions_unused, srp_exceptions, srp_scopes, srp_effects with
                    (* TODO: maybe write a function to simplify the construction of such strings *)
                      | true, true, true, true -> assert false
                      | false, true, true, true -> "unused conditions"
                      | true, false, true, true -> "exceptions"
                      | true, true, false, true -> "scopes"
                      | true, true, true, false -> "effects"
                      | false, false, true, true -> "unused conditions and exceptions"
                      | false, true, false, true -> "unused conditions and scopes"
                      | false, true, true, false -> "unused conditions and effects"
                      | true, false, false, true -> "exceptions and scopes"
                      | true, false, true, false -> "exceptions and effects"
                      | true, true, false, false -> "scopes and effects"
                      | true, false, false, false -> "exceptions, scopes, and effects"
                      | false, false, false, true -> "unused conditions, exceptions and scopes"
                      | false, false, true, false -> "unused conditions, exceptions and effects"
                      | false, true, false, false -> "unused conditions, scopes and effects"
                      | false, false, false, false -> "unused conditions, exceptions, scopes, and effects"
                    in
                    Impossible (ERule (pos, "can't make selected conditions Sup, because " ^ not_srp ^ " are not SRP"))
                | None ->
                  Impossible (ERule (pos, "no conditions are marked as suppressing"))
          in
          let verdict_effects =
            if cause_effects then
              if srp_exceptions && srp_scopes && srp_conditions then
                type_pattern_with_formulas tr s pos pols Cau f2 q
              else
                let not_srp = match srp_exceptions, srp_scopes, srp_conditions with
                  (* TODO: maybe write a function to simplify the construction of such strings *)
                  | true, true, true -> assert false
                  | false, true, true -> "exceptions"
                  | true, false, true -> "scopes"
                  | true, true, false -> "conditions"
                  | false, false, true -> "exceptions and scopes"
                  | false, true, false -> "exceptions and conditions"
                  | true, false, false -> "scopes and conditions"
                  | false, false, false -> "exceptions, scopes, and conditions"
                in
                Impossible (ERule (pos, "can't make effects Cau, because " ^ not_srp ^ " are not SRP"))
            else Impossible (ERule (pos, "effects are not marked as causing"))
          in
          let verdict_rule_implication = conj verdict_conditions verdict_effects |> conj verdict in
          begin match verdict_rule_implication with
            | Possible _ -> verdict_rule_implication
            | Impossible e ->
              let err_msg = Printf.sprintf "Impossible, rule is not transparently enforceable: %s" (Errors.to_string e) in
              Util.enf_error err_msg (Some pos)
          end
      end
    | TCDefinition (idx, _, _, f1, p, exceptions, scopes, _, f2) ->
      let e = get_predicate_name f2 in
      let pos = try snd (Map.find_exn s.rule_tree.label_of_rule idx) with _ -> assert false in
      let ex_neg = List.map exceptions ~f:(fun (p, f) -> (p, Tformula.tneg f)) in
      let aux d =
        let v_pols = solve d in
        (* TODO: test enforcability checking and remove assertion after successful testing *)
        assert (List.length v_pols = 1); (* If assertion fails, dnf function is wrong *)
        let v_pols = List.hd_exn v_pols in
        let t, itl_srp = begin match Map.find v_pols e with
          | Some (t, true) -> t, Some itl_itvs_and_stricts
          | Some (t, false) -> t, None
          | None -> Obs, None (* TODO: is Obs desired here, or should it be something else like Non? *)
        end in
        let pols_tr = update_pols_with_transparency_conditions pols v_pols in
        let verdict_exceptions = type_pattern_with_formulas itl_srp s pos pols_tr t ex_neg TPPresent in
        let verdict_scopes = type_pattern_with_formulas itl_srp s pos pols_tr t scopes TPPresent in
        let verdict_conditions = type_pattern_with_formulas itl_srp s pos pols_tr t f1 p in
        match t with
        | Cau -> (* all parts of the definition must be Cau *)
          let verdict_references = conj verdict_exceptions verdict_scopes in
          conj (conj verdict_conditions verdict_references) verdict
        | Sup -> (* only one part of the definition must be Sup *)
          let verdict_references = disj verdict_exceptions verdict_scopes in
          conj (disj verdict_conditions verdict_references) verdict
        | Obs -> verdict
        | _ -> assert false
      in
      let verdicts = List.map dnf_of_v ~f:aux in
      List.fold ~f:disj ~init:(Impossible (EInit (Some pos))) verdicts
    | TCDefinitionDis (disjuncts, g) ->
      let e = get_predicate_name g in
      let aux d =
        let v_pols = solve d in
        (* TODO: test enforcability checking and remove assertion after successful testing *)
        assert (List.length v_pols = 1); (* If assertion fails, dnf function is wrong *)
        let v_pols = List.hd_exn v_pols in
        let t, itl_srp = begin match Map.find v_pols e with
          | Some (t, true) -> t, Some itl_itvs_and_stricts
          | Some (t, false) -> t, None
          | None -> Obs, None (* TODO: is Obs desired here, or should it be something else like Non? *)
        end in
        let pols_tr = update_pols_with_transparency_conditions pols v_pols in
        let type_disjunct (_, _, pos, f, p, exceptions, scopes, cs) =
          let f = f @ (add_pos pos cs) in (* combine renaming conditions with the actual conditions of the constitutive rule *)
          let ex_neg = List.map exceptions ~f:(fun (p, f) -> (p, Tformula.tneg f)) in
          let verdict_exceptions = type_pattern_with_formulas itl_srp s pos pols_tr t ex_neg TPPresent in
          let verdict_scopes = type_pattern_with_formulas itl_srp s pos pols_tr t scopes TPPresent in
          let verdict_conditions = type_pattern_with_formulas itl_srp s pos pols_tr t f p in
          begin match t with
            | Cau -> (* all parts of the definition must be Cau *)
              let verdict_references = conj verdict_exceptions verdict_scopes in
              conj (conj verdict_conditions verdict_references) verdict
            | Sup -> (* only one part of the definition must be Sup *)
              let verdict_references = disj verdict_exceptions verdict_scopes in
              conj (disj verdict_conditions verdict_references) verdict
            | Obs -> verdict
            | _ -> assert false
          end
        in
        Map.map disjuncts ~f:type_disjunct
        |> Map.data
        |> List.fold ~f:disj ~init:(Impossible (EInit None))
        |> conj verdict
      in
      let verdicts = List.map dnf_of_v ~f:aux in
      List.fold ~f:disj ~init:(Impossible (EInit None)) verdicts

let check_used_events_are_defined (tprog: Tlex.tprog) def use =
  let all_defined_events = List.concat (Map.data def)
                           |> List.dedup_and_sort
                              ~compare:String.compare in
  let check_used_are_defined idx =
    let used = Map.find_exn use idx in
    let pos = Map.find_exn tprog.rule_tree.label_of_rule idx |> snd in
    List.iter used ~f:(fun name ->
      if not (List.mem all_defined_events name ~equal:String.equal) then
        let err_msg = Printf.sprintf
            "Internal event \"%s\" is used but never constituted (defined)"
            name in
        Util.enf_error err_msg (Some pos)) in
  Map.iter_keys use ~f:check_used_are_defined

let relative_interval_of_formula_conjunct itl_itvs f =
  let fs = List.map f ~f:snd in
  let itvs = (List.map fs ~f:(relative_interval ~itl_itvs:itl_itvs)) in
  List.fold itvs ~init:Zinterval.full ~f:Zinterval.lub

let relative_interval_of_pattern_with_formulas itl_itvs f: tpattern -> Zinterval.t = function
  | TPPresent -> relative_interval_of_formula_conjunct itl_itvs f
  | TPEventually i
  | TPAlways i ->
    let i = Zinterval.of_interval i in
    let j = relative_interval_of_formula_conjunct itl_itvs f in
    Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
  | TPUntil (i, g) ->
    let i = Zinterval.of_interval i in
    let j = relative_interval_of_formula_conjunct itl_itvs f in
    Zinterval.lub 
      (Zinterval.sum (Zinterval.to_zero i) (relative_interval ~itl_itvs:itl_itvs g))
      (Zinterval.sum i j)
  | TPOnce i
  | TPHistorically i ->
    let i = Zinterval.of_interval i in
    let j = relative_interval_of_formula_conjunct itl_itvs f in
    Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
  | TPSince (i, g) ->
    let i = Zinterval.of_interval i in
    let j = relative_interval_of_formula_conjunct itl_itvs f in
    Zinterval.lub
      (Zinterval.sum (Zinterval.to_zero i) j)
      (Zinterval.sum i (relative_interval ~itl_itvs:itl_itvs g))

let strict_of_formula_conjunct itl_strict f =
  let fs = List.map f ~f:snd in
  List.for_all fs ~f:(strict ~itl_strict:itl_strict)

let strict_of_pattern_with_formulas itl_strict f: tpattern -> bool = function
  | TPPresent -> strict_of_formula_conjunct itl_strict f
  | TPEventually i
  | TPAlways i ->
    let i = Zinterval.of_interval i in
    not (Zinterval.mem 0 i)
    && strict_of_formula_conjunct itl_strict f
  | TPUntil (i, g) ->
    let i = Zinterval.of_interval i in
    not (Zinterval.mem 0 (Zinterval.inv i))
    && strict_of_formula_conjunct itl_strict f
    && strict ~itl_strict:itl_strict g
  | TPOnce _
  | TPHistorically _ -> strict_of_formula_conjunct itl_strict f
  | TPSince (_, g) ->
    strict_of_formula_conjunct itl_strict f
    && strict ~itl_strict:itl_strict g

let relative_interval_of_disjunct itl_itvs (_, _, _, f, p, e, s, _) =
  (* The relative interval of the "variable renaming conditions" will always be 0 and is thus ignored *)
  let conditions_itv = relative_interval_of_pattern_with_formulas itl_itvs f p in
  let exceptions_itv = relative_interval_of_pattern_with_formulas itl_itvs e TPPresent in
  let scopes_itv = relative_interval_of_pattern_with_formulas itl_itvs s TPPresent in
  Zinterval.lub conditions_itv exceptions_itv |> Zinterval.lub scopes_itv

let relative_interval_itl itl_itvs = function
  (* requires that all relative intervals of events used in the given rule have already been computed *)
  | TCDefinition (_, _, _, f, p, e, s, _, Tformula.TPredicate (name, _, _)) ->
    let conditions_itv = relative_interval_of_pattern_with_formulas itl_itvs f p in
    let exceptions_itv = relative_interval_of_pattern_with_formulas itl_itvs e TPPresent in
    let scopes_itv = relative_interval_of_pattern_with_formulas itl_itvs s TPPresent in
    let itv = Zinterval.lub conditions_itv exceptions_itv |> Zinterval.lub scopes_itv in
    Map.add_exn itl_itvs ~key:name ~data:itv
  | TCDefinition _ -> assert false (* final formula must be a predicate *)
  | TCDefinitionDis (disjuncts, Tformula.TPredicate (name, _, _)) ->
    let relative_itvs_disjuncts = List.map (Map.data disjuncts) ~f:(relative_interval_of_disjunct itl_itvs) in
    let itv = List.fold relative_itvs_disjuncts ~init:Zinterval.full ~f:Zinterval.lub in
    Map.add_exn itl_itvs ~key:name ~data:itv
  | TCDefinitionDis _ -> assert false (* final formula must be a predicate *)
  | _ -> itl_itvs


let strict_of_disjunct itl_strict (_, _, _, f, p, e, s, _) =
  (* The "variable renaming conditions" will always be strict and are thus ignored *)
  let conditions_strict = strict_of_pattern_with_formulas itl_strict f p in
  let exceptions_strict = strict_of_pattern_with_formulas itl_strict e TPPresent in
  let scopes_itv = strict_of_pattern_with_formulas itl_strict s TPPresent in
  conditions_strict && exceptions_strict && scopes_itv

let strict_itl itl_strict = function
  (* requires that all "strictness"-constraints of events used in the given rule have already been computed *)
  | TCDefinition (_, _, _, f, p, e, s, _, Tformula.TPredicate (name, _, _)) ->
    let conditions_strict = strict_of_pattern_with_formulas itl_strict f p in
    let exceptions_strict = strict_of_pattern_with_formulas itl_strict e TPPresent in
    let scopes_itv = strict_of_pattern_with_formulas itl_strict s TPPresent in
    let is_strict = conditions_strict && exceptions_strict && scopes_itv in
    Map.add_exn itl_strict ~key:name ~data:is_strict
  | TCDefinition _ -> assert false
  | TCDefinitionDis (disjuncts, Tformula.TPredicate (name, _, _)) ->
    let is_strict = List.for_all (Map.data disjuncts) ~f:(strict_of_disjunct itl_strict) in
    Map.add_exn itl_strict ~key:name ~data:is_strict
  | TCDefinitionDis _ -> assert false
  | _ -> itl_strict

let type_trules_compilation (tprog:Tlex.tprog) (compilation_rules: (int, trule_compilation, 'a) Map.t) : ((string, EnfType.t * bool, 'b) Map.t * int list) =
  let def_internal = def_sets compilation_rules tprog.tevents in
  let use_internal = use_sets compilation_rules tprog.tevents in
  check_used_events_are_defined tprog def_internal use_internal;
  let sorted_rule_indices = topological_sort (Map.keys compilation_rules) def_internal use_internal in
  let compilation_rules_sorted = List.map sorted_rule_indices ~f:(fun idx -> Map.find_exn compilation_rules idx) in
  let itl_itvs = List.fold (List.rev compilation_rules_sorted) ~f:relative_interval_itl ~init:(Map.empty (module String)) in
  let itl_strict = List.fold (List.rev compilation_rules_sorted) ~f:strict_itl ~init:(Map.empty (module String)) in
  let verdict = List.fold compilation_rules_sorted ~f:(type_trule_compilation (itl_itvs, itl_strict) tprog) ~init:(Possible CTT) in
  let constraints = match verdict with
    | Possible c -> c
    | Impossible e ->
      let err_msg = Printf.sprintf "Impossible: %s" (Errors.to_string e) in
      Util.enf_error err_msg None
  in
  let possible_policies = Constraints.solve constraints in
  let found_pol_constraints = match List.hd possible_policies with
    | Some c -> c
    | None -> Map.empty (module String)
  in
  found_pol_constraints, sorted_rule_indices

let collect_constitutive_rules (tprog: Tlex.tprog) : (Lexing.position * int * trule * (Lexing.position * Tformula.t) list * (Lexing.position * Tformula.t) list) list =
  List.filter_map tprog.tstmts ~f:(function
    | TSRule (pos, idx, _, _, trule, _) ->
      let exceptions = get_exception_predicates ~negated:false tprog idx in
      let scopes = get_scope_predicates tprog idx in
      begin match trule with
        | TConstitutive _
        | TExceptionC _ ->
          Some (pos, idx, trule, exceptions, scopes)
        | _ -> None
      end
    | _ -> None)

let combine_constitutive_rules (rules: (Lexing.position * int * trule * (Lexing.position * Tformula.t) list * (Lexing.position * Tformula.t) list) list) : trule_compilation list =
  let collect_and_separate_event_definitions m (pos, idx, rule, exceptions, scopes) =
    let trule_type = match rule with
      | TConstitutive _ -> TRTConstitutive
      | TExceptionC _ -> TRTExceptionC
      | _ -> assert false
    in
    let separate_event_definitions f1 p (m': (string, 'a, 'b) Map.t) (_, f) = match f with
      | Tformula.TPredicate (name, terms, _) ->
        let d = (idx, trule_type, pos, f1, exceptions, scopes, p, terms) in
        Map.add_multi m' ~key:name ~data:d
      | _ -> assert false
    in
    match rule with
    | TConstitutive (f1, p, f2)
    | TExceptionC (f1, p, _, _, f2) ->
      List.fold f2 ~init:m ~f:(separate_event_definitions f1 p)
    | _ -> assert false
  in
  let event_def_map = List.fold rules ~init:(Map.empty (module String)) ~f:collect_and_separate_event_definitions in
  let replace_variables (idx, trule_type, pos, f1, exceptions, scopes, p, terms) =
    let terms' = List.fold terms
                    ~init:([],0)
                    ~f:(fun (ts,i) t
                        -> Term.{trm=TVar ("__t" ^ string_of_int i); tt=t.tt}::ts, i+1)
                 |> fst in
    let term_conditions = List.map2_exn terms terms' ~f:(fun t1 t2 -> Tformula.TEqConst (t1, t2)) in
    (idx, trule_type, pos, f1, exceptions, scopes, term_conditions, p, terms')
  in
  let event_map_renamed = Map.map event_def_map ~f:(List.map ~f:replace_variables) in
  let extract_terms (_,_,_,_,_,_,_,_,terms) : Tformula.Term.t list = terms in
  let to_tr_def_dis ((name,definitions): (string * 'z)) =
    let add_disjunct_to_map ((m, k): (int, 'x, 'y) Map.t * int) (idx, trt, pos, f, exceptions, scopes, cs, p, _) =
      let data = (idx, trt, pos, f, p, exceptions, scopes, cs) in
      Map.add_exn m ~key:k ~data:data, k+1
    in
    let disjunction = List.fold definitions
                        ~init:(Map.empty (module Int), 0)
                        ~f:add_disjunct_to_map
                      |> fst
    in
    let terms = Map.find_exn event_map_renamed name
                |> List.hd_exn
                |> extract_terms in
    TCDefinitionDis (disjunction, Tformula.TPredicate (name, terms, Lex.Predicate))
  in
  Map.to_alist event_map_renamed |> List.map ~f:to_tr_def_dis

let create_def_dis_rules tprog =
  let constitutive_rules = collect_constitutive_rules tprog in
  combine_constitutive_rules constitutive_rules

let create_def_rules tprog =
  List.filter_map tprog.tstmts ~f:(function
    | TSRule (pos, idx, _, _, trule, _) ->
      let exceptions = get_exception_predicates ~negated:false tprog idx in
      let scopes = get_scope_predicates tprog idx in
      begin match trule with
        | TScope (f1, p, r, f2)
          -> Some (TCDefinition (idx, TRTScope, pos, f1, p, exceptions, scopes, r, f2))
        | TException (f1, p, r, f2)
          -> Some (TCDefinition (idx, TRTException, pos, f1, p, exceptions, scopes, r, f2))
        | TExceptionC (f1, p, r, f2, _)
          -> Some (TCDefinition (idx, TRTExceptionC, pos, f1, p, exceptions, scopes, r, f2))
        | _ -> None
      end
    | _ -> None)

let create_imp_rules tprog =
  List.filter_map tprog.tstmts ~f:(function
    | TSRule (pos, idx, _, _, trule, _) ->
      let exceptions = get_exception_predicates ~negated:true tprog idx in
      let scopes = get_scope_predicates tprog idx in
      begin match trule with
        | TObligation (f1, p, f2, q, rt, rcs)
          -> Some (TCImplication (idx, TRTObligation, pos, f1, p, exceptions, scopes, f2, q, rt, rcs))
        | TPermission (f1, p, f2, q, rt, rcs)
          -> Some (TCImplication (idx, TRTPermission, pos, f1, p, exceptions, scopes, f2, q, rt, rcs))
        | _ -> None
      end
    | _ -> None)

let create_compilation_rules (tprog: Tlex.tprog) : (int, trule_compilation, Int.comparator_witness) Map.t =
  let def_dis_rules = create_def_dis_rules tprog in
  let def_rules = create_def_rules tprog in
  let imp_rules = create_imp_rules tprog in
  List.fold (def_dis_rules @ def_rules @ imp_rules)
            ~init:((Map.empty (module Int), 0))
            ~f:(fun (m,i) r -> (Map.add_exn m ~key:i ~data:r, i+1))
  |> fst

let convert_pattern_with_formulas (s: tprog) (enftype: EnfType.t) pols (fs: (Lexing.position * Tformula.t) list list) (p: tpattern) : ((Lexing.position * Eformula.t) list list * epattern) =
  match enftype with
  | Cau ->
    let convert_ b enftype (pos, f) = match convert s pols b enftype f with
      | Some f -> (pos, f)
      | None -> let err_msg = "The formula\n" ^ Tformula.to_string f ^ "\ncannot be converted under policy " ^ EnfType.to_string enftype ^ "." in
                Util.enf_error err_msg (Some pos)
    in
    let convert_formulas f = List.map f ~f:(fun f -> List.map f ~f:(convert_ (C Lextime.Span.zero) enftype)) in (* TODO: what is the correct bound value? is zero correct?*)
    begin match p with
      | TPPresent -> convert_formulas fs, EPPresent
      (* | TPEventually i -> assert false *)
      (* | TPAlways i -> assert false *)
      (* | TPUntil (i, g) -> assert false *)
      (* | TPOnce i -> assert false *)
      (* | TPHistorically i -> assert false *)
      (* | TPSince (i, g) -> assert false *)
      | _ -> assert false
    end
  | Sup ->
    begin match p with
      | TPPresent ->
        assert false
      (* | TPEventually i -> assert false *)
      (* | TPAlways i -> assert false *)
      (* | TPUntil (i, g) -> assert false *)
      (* | TPOnce i -> assert false *)
      (* | TPHistorically i -> assert false *)
      (* | TPSince (i, g) -> assert false *)
      | _ -> assert false
    end
  | Obs -> 
    begin match p with
      (* | TPPresent -> assert false *)
      (* | TPEventually i -> assert false *)
      (* | TPAlways i -> assert false *)
      (* | TPUntil (i, g) -> assert false *)
      (* | TPOnce i -> assert false *)
      (* | TPHistorically i -> assert false *)
      (* | TPSince (i, g) -> assert false *)
      | _ -> assert false
    end
  | _ -> assert false

let convert_compilation_rule (s: tprog) pols = function
  | TCImplication (idx, trt, pos, f1, p, exceptions, scopes, f2, q, rt, rcs) ->
    let f1s, p_e = convert_pattern_with_formulas s Sup pols [f1;exceptions;scopes] p in
    let f2s, q_e = convert_pattern_with_formulas s Cau pols [f2] q in
    let f1_e, e_e, s_e = match f1s with
      | [f1;exceptions;scopes] -> f1, exceptions, scopes
      | _ -> assert false
    in
    let f2_e = match f2s with
      | [f2] -> f2
      | _ -> assert false
    in
    let ert = erule_type_from_trule_type trt in
    ECImplication (idx, ert, pos, f1_e, p_e, e_e, s_e, f2_e, q_e, rt, rcs)
  | TCDefinition (idx, trt, pos, f1, p, exceptions, scopes, refs, f2) ->
    let pred_name = match f2 with
      | Tformula.TPredicate (name, _, _) -> name
      | _ -> assert false
    in
    let enftype = match Map.find pols pred_name with
      | Some t -> t
      | None -> Obs
    in
    let f1s, p_e = convert_pattern_with_formulas s enftype pols [f1;exceptions;scopes] p in
    let f1_e, e_e, s_e = match f1s with
      | [f1;exceptions;scopes] -> f1, exceptions, scopes
      | _ -> assert false
    in
    let f2_e = match convert s pols (C Lextime.Span.zero) enftype f2 with (* TODO what is the correct/expected value for the bound `b`? *)
      | Some f2_e -> f2_e
      | None -> Util.enf_error ("Internal predicate \"" ^ Tformula.to_string f2 ^ "\" cannot be converted.") None (* TODO, should this be replaced with assert false/ why might this happen, could it even happen after enforcement checking? *)
    in
    let ert = erule_type_from_trule_type trt in
    ECDefinition (idx, ert, pos, f1_e, p_e, e_e, s_e, refs, f2_e) 
  | TCDefinitionDis (disjuncts, g) ->
    let pred_name = match g with
      | Tformula.TPredicate (name, _, _) -> name
      | _ -> assert false
    in
    let enftype = match Map.find pols pred_name with
      | Some t -> t
      | None -> Obs
    in
    let g_e = match convert s pols (C Lextime.Span.zero) enftype g with (* TODO what is the correct/expected value for the bound `b`? *)
      | Some g_e -> g_e
      | None -> Util.enf_error ("Internal predicate \"" ^ Tformula.to_string g ^ "\" cannot be converted.") None (* TODO, should this be replaced with assert false/ why might this happen, could it even happen after enforcement checking? *)
    in
    let convert_disjunct (idx, trt, pos, f1, p, exceptions, scopes, cs) =
      let cs = List.map cs ~f:(fun c -> Lexing.dummy_pos, c) in
      let f1s, p_e = convert_pattern_with_formulas s enftype pols [f1;exceptions;scopes;cs] p in
      let f1_e, e_e, s_e, cs_e = match f1s with
        | [f1;exceptions;scopes;cs] -> f1, exceptions, scopes, List.map cs ~f:snd
        | _ -> assert false
      in
      let ert = erule_type_from_trule_type trt in
      idx, ert, pos, f1_e, p_e, e_e, s_e, cs_e
    in
    let disjuncts_e = Map.map disjuncts ~f:convert_disjunct in
    ECDefinitionDis (disjuncts_e, g_e)

let convert_compilation_rules tprog pols rules =
  Map.map rules ~f:(convert_compilation_rule tprog pols)

let erules_from_compilation_rules (compilation_rules: (int, trule_compilation, Int.comparator_witness) Map.t) : (int, erule, Int.comparator_witness) Map.t =
  let c_rules = Map.to_alist compilation_rules in
  let aux erules (c_idx, c_rule) = match c_rule with
    | TCImplication (r_idx, trt, _, _, _, _, _, _, _, _, _) ->
      begin match trt with
        | TRTObligation -> Map.add_exn erules ~key:r_idx ~data:(EObligation c_idx)
        | TRTPermission -> Map.add_exn erules ~key:r_idx ~data:(EPermission c_idx)
        | _ -> assert false
    end
    | TCDefinition (r_idx, trt, _, _, _, _, _, _, _) ->
      begin match trt with
        | TRTException -> Map.add_exn erules ~key:r_idx ~data:(EException c_idx)
        | TRTExceptionC -> Map.update erules r_idx ~f:(function
            | Some (EExceptionC (-1, constitutives)) -> EExceptionC (c_idx, constitutives)
            | Some _ -> assert false (* not -1: exception cannot be defined already *)
            | None -> EExceptionC (c_idx, []))
        | TRTScope -> Map.add_exn erules ~key:r_idx ~data:(EScope c_idx)
        | _ -> assert false
      end
    | TCDefinitionDis (disjunct_map, _) ->
      let add_disjuncts_to_map m (d_idx, (r_idx, trt, _, _, _, _, _, _)) =
        begin match trt with
          | TRTConstitutive ->
            Map.update m r_idx ~f:(function
              | Some (EConstitutive ds) -> EConstitutive ((c_idx, d_idx)::ds)
              | Some _ -> assert false
              | None -> EConstitutive [(c_idx, d_idx)])
          | TRTExceptionC ->
            Map.update m r_idx ~f:(function
              | Some (EExceptionC (c_idx_ex, constitutives)) -> EExceptionC (c_idx_ex, (c_idx, d_idx)::constitutives)
              | Some _ -> assert false
              | None -> EExceptionC (-1, [(c_idx, d_idx)]))
          | _ -> assert false
        end
      in
      Map.to_alist disjunct_map |> List.fold ~init:erules ~f:add_disjuncts_to_map
  in
  List.fold c_rules ~f:aux ~init:(Map.empty (module Int))

let do_type _ (tprog: Tlex.tprog) : Elex.eprog =
  let compilation_rules  = create_compilation_rules tprog in
  let pols, rule_order = type_trules_compilation tprog compilation_rules in
  let pols = Map.map pols ~f:fst in
  let erules = erules_from_compilation_rules compilation_rules in
  let e_compilation_rules = convert_compilation_rules tprog pols compilation_rules in
  {
    estmts     = List.map tprog.tstmts ~f:(type_tstmt erules);
    ealiases   = tprog.taliases;
    eevents    = tprog.tevents;
    efunctions = tprog.tfunctions;
    variables  = tprog.variables;
    rule_tree  = tprog.rule_tree;
    compilation_rules = e_compilation_rules;
    compilation_order = rule_order;
    pols = pols;
  }
