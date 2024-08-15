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

type pg_map = (string, (string, bool, String.comparator_witness) Map.t, String.comparator_witness) Map.t
let xand a b = (a && b) || (not a && not b)

let rec is_past_guarded ?(pg_map: pg_map=Map.empty (module String)) s x p f =
  let r =
  match f.f with
  | TTT | TFF -> false
  | TEqConst (x', y) -> p && TTerm.equal_core (TTerm.TVar x) x'.trm && TTerm.is_const y.trm
  | TPredicate (e, ts, _) ->
    begin match Map.find s.tevents e with
      | Some (_, _, TItl, _) ->  xand p (Map.find_exn (Map.find_exn pg_map e) x)
      | _ -> List.exists ~f:(fun t -> TTerm.equal_core (TTerm.TVar x) t.trm) ts
    end
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
    | EFormula of string option * t * EnfType.t
    | EFormulaTransparent of string option * t * EnfType.t
    | EFormulasTransparent of (string * string) option * t list * EnfType.t
    | EConj of error * error
    | EDisj of error * error
    | EPattern of Lexing.position * string * tpformula * EnfType.t
    | ERule of Lexing.position * string

  let rec to_string ?(n=0) e =
    let sp = Util.spaces (2*n) in
    let lb = "\n" ^ sp in
    begin match e with
      | ECast (e, t', _, t, false) ->
        Printf.sprintf
          "make %s %s (currently, it has type %s)"
          e
          (EnfType.to_string t)
          (EnfType.to_string t')
      | ECast (e, t', false, t, true) ->
        Printf.sprintf
          "make %s %s:Transparent (currently, it has type %s, transparency is not the issue as it gets assumed)"
          e
          (EnfType.to_string t)
          (EnfType.to_string t')
      | ECast (e, t', true, t, true) ->
        Printf.sprintf
          "make %s %s:Transparent (currently, it has type %s:Transparent)"
          e
          (EnfType.to_string t)
          (EnfType.to_string t')
      | EFormula (None, f, t) ->
        Printf.sprintf
          "make %s %s, but this is impossible at\n %s\n"
          (Tformula.to_string f)
          (EnfType.to_string t)
          (Util.string_of_positions f.positions)
      | EFormula (Some s, f, t) ->
        Printf.sprintf
          "make %s %s, but this is impossible (%s) at:\n%s\n"
          (Tformula.to_string f)
          (EnfType.to_string t)
          s
          (Util.string_of_positions f.positions)
      | EFormulaTransparent (None, f, t) ->
        Printf.sprintf
          "make %s %s, but this is impossible at:\n%s\n"
            (Tformula.to_string f)
            (EnfType.to_string t)
            (Util.string_of_positions f.positions)
      | EFormulaTransparent (Some s, f, t) ->
          Printf.sprintf
            "make %s %s (transparent), but this is impossible (%s) at:\n%s\n"
            (Tformula.to_string f)
            (EnfType.to_string t)
            s
            (Util.string_of_positions f.positions)
      | EFormulasTransparent (None, fs, t) ->
        Printf.sprintf
          "make %s %s (transparent), but this is impossible at:\n%s\n"
          (List.map ~f:Tformula.to_string fs |> Util.string_of_string_list)
          (EnfType.to_string t)
          (List.concat_map fs ~f:(fun f -> f.positions) |> Util.string_of_positions)
      | EFormulasTransparent (Some (op, s), fs, t) ->
          Printf.sprintf
            "make the formulas %s under opreation %s %s (transparent), but this is impossible (%s) at:\n%s\n"
            (List.map ~f:Tformula.to_string fs |> Util.string_of_string_list)
            op
            (EnfType.to_string t)
            s
            (List.concat_map fs ~f:(fun f -> f.positions) |> Util.string_of_positions)
      | EConj (f, g) ->
        Printf.sprintf
          "both%s* %s%sand%s* %s"
          lb
          (to_string ~n:(n+1) f)
          lb
          lb
          (to_string ~n:(n+1) g)
      | EDisj (f, g) ->
        Printf.sprintf
          "either%s* %s%sor%s* %s"
          lb
          (to_string ~n:(n+1) f)
          lb
          lb
          (to_string ~n:(n+1) g)
      | EPattern (pos, msg, tpf, t) ->
        Printf.sprintf
          "make %s %s, but this is impossible at %s because of %s" (* TODO: incorporate formual list in error message *)
          (string_of_tpattern tpf.p)
          (EnfType.to_string t)
          (Util.string_of_pos pos)
          msg
      | ERule (pos, msg) ->
        Printf.sprintf
          "%s at %s"
          msg
          (Util.string_of_pos pos)
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

  let conj' = function
    | [] -> Possible CTT
    | c::cs -> List.fold cs ~init:c ~f:conj

  let disj' = function
    | [] -> Possible CFF
    | c::cs -> List.fold cs ~init:c ~f:disj

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

let rec types s pols (t: EnfType.t) (f: Tformula.t) =
  let error s = Impossible (EFormula (Some s, f, t)) in
  let types_predicate = types_predicate false in (* set transparency requirement to false *)
  let types = types s pols in (* fix `types` function with invariant parameters *)
  match t with
  | Cau -> begin
      match f.f with
      | TTT -> Possible CTT
      | TPredicate (e, _, _) -> types_predicate pols Cau e
      | TNeg f -> types Sup f
      | TAnd (_, fs) -> Constraints.conj' (List.map fs ~f:(types Cau))
      | TOr (L, fs) -> types Cau (List.hd_exn fs)
      | TOr (R, fs) -> types Cau (List.last_exn fs)
      | TOr (_, fs) -> Constraints.disj' (List.map fs ~f:(types Cau))
      | TImp (L, f, _) -> types Sup f
      | TImp (R, _, g) -> types Cau g
      | TImp (_, f, g) -> disj (types Sup f) (types Cau g)
      | TIff (L, L, f, _) -> conj (types Sup f) (types Cau f)
      | TIff (L, R, f, g) -> conj (types Sup f) (types Sup g)
      | TIff (R, L, f, g) -> conj (types Cau g) (types Cau f)
      | TIff (R, R, _, g) -> conj (types Cau g) (types Sup g)
      | TIff (_, _, f, g) -> conj (disj (types Sup f) (types Cau g))
                                  (disj (types Cau f) (types Sup g))
      | TExists (_, f) -> types Cau f
      | TForall (x, f) when is_past_guarded s x false f -> types Cau f
      | TForall (x, _) -> error ("for causability " ^ x ^ " must be past-guarded")
      | TNext (i, f) when Interval.equal i Interval.full -> types Cau f
      | TNext _ -> error "○ with non-[0,∞) interval is never Cau"
      | TOnce (i, g) | TSince (_, i, _, g) when Interval.has_zero i -> types Cau g
      | TOnce _ | TSince _ -> error "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      | TEventually (_, f) | TAlways (_, f) -> types Cau f
      | TUntil (LR, B _, f, g) -> conj (types Cau f) (types Cau g)
      | TUntil (_, i, _, g) when Interval.has_zero i -> types Cau g (* in the non-transparent case when i is unbounded, an artificial bound will be added during conversion *)
      | TUntil (_, _, f, g) -> conj (types Cau f) (types Cau g) (* in the non-transparent case when i is unbounded, an artificial bound will be added during conversion *)
      | TPrev _ -> error "● is never Cau"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Sup -> begin
      match f.f with
      | TFF -> Possible CTT
      | TPredicate (e, _, _) -> types_predicate pols Sup e
      | TNeg f -> types Cau f
      | TAnd (L, fs) -> types Sup (List.hd_exn fs)
      | TAnd (R, fs) -> types Sup (List.last_exn fs)
      | TAnd (_, fs) -> Constraints.disj' (List.map fs ~f:(types Sup))
      | TOr (_, fs) -> Constraints.conj' (List.map fs ~f:(types Sup))
      | TImp (_, f, g) -> conj (types Cau f) (types Sup g)
      | TIff (L, _, f, g) -> conj (types Cau f) (types Sup g)
      | TIff (R, _, f, g) -> conj (types Sup f) (types Cau g)
      | TIff (_, _, f, g) -> disj (conj (types Cau f) (types Sup g))
                                  (conj (types Sup f) (types Cau g))
      | TExists (x, f) when is_past_guarded s x true f -> types Sup f
      | TExists (x, _) -> error ("for suppressability " ^ x ^ " must be past-guarded")
      | TForall (_, f) -> types Sup f
      | TNext (_, f) -> types Sup f
      | THistorically (i, f) when Interval.has_zero i -> types Sup f
      | THistorically _ -> error "■[a,b) with a > 0 is never Sup"
      | TSince (_, i, f, _) when not (Interval.has_zero i) -> types Sup f
      | TSince (_, _, f, g) -> conj (types Sup f) (types Sup g)
      | TEventually (_, f) | TAlways (_, f) -> types Sup f
      | TUntil (L, i, f, _) when not (Interval.has_zero i) -> types Sup f
      | TUntil (R, _, _, g) -> types Sup g
      | TUntil (_, i, f, g) when not (Interval.has_zero i) -> disj (types Sup f) (types Sup g)
      | TUntil (_, _, _, g) -> types Sup g
      | TPrev _ -> error "● is never Sup"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Obs -> Possible CTT
  | _ -> Impossible (EFormula (None, f, t))

let rec types_transparent itvls stricts s pols (t: EnfType.t) (f: Tformula.t) : verdict =
  let error_tr s = Impossible (EFormulaTransparent (Some s, f, t)) in
  let error s = Impossible (EFormula (Some s, f, t)) in
  let types_transparent = types_transparent itvls stricts s pols in
  let srp = strictly_relative_past ~itl_itvs_and_strict:(itvls, stricts) in
  let types_predicate = types_predicate true in (* Set transparency requirement to true *)
  match t with
  | Cau -> begin
      match f.f with
      | TTT -> Possible CTT
      | TPredicate (e, _, _) -> types_predicate pols Cau e
      | TNeg f -> types_transparent Sup f
      | TAnd (_, fs) -> Constraints.conj' (List.map fs ~f:(types_transparent Cau))
      (* OR:Cau is typed analogously to AND:Sup *)
      | TOr (L, fs) when List.for_all (List.drop fs 1) ~f:srp -> types_transparent Cau (List.hd_exn fs)
      | TOr (L, _) -> error_tr "∨:L (Cau) is only transparently enforceable when all formulas except for the left-most are SRP, but at least one of them is not SRP"
      | TOr (R, fs) when List.for_all (List.drop_last_exn fs) ~f:srp -> types_transparent Cau (List.last_exn fs)
      | TOr (R, _) -> error_tr "∨:R (Cau) is only transparently enforceable when all formulas except for the right-most are SRP, but at least one of them is not SRP"
      | TOr (_, fs) ->
        let are_others_srp = Util.lists_with_one_removed fs |> List.map ~f:(List.for_all ~f:srp) in
        let is_srp_to_verdict f = function
          | true -> Possible CTT
          | false ->
            let msg = Printf.sprintf "∨ (Cau) is transparently enforceable when all formulas besides the one used for enforcement (%s) are SRP, but at least one of them is not SRP" (Tformula.to_string f) in
            error_tr msg
        in
        let types_and_srp f srp = conj (types_transparent Cau f) (is_srp_to_verdict f srp) in
        let vs = (List.map2_exn fs are_others_srp ~f:types_and_srp) in
        Constraints.disj' vs
      (* (a IMP b):Cau <==> (not a OR b):Cau -> thus IMP:Cau is typed analogously to AND:Sup *)
      | TImp (L, f, g) when srp g -> types_transparent Sup f
      | TImp (L, _, _) -> error_tr "→:L (Cau) is only transparently enforceable when the RHS is SRP"
      | TImp (R, f, g) when srp f -> types_transparent Cau g
      | TImp (R, _, _) -> error_tr "→:R (Cau) is only transparently enforceable when the LHS is SRP"
      | TImp (_, f, g) ->
        let srp_of_other_side other =
          if srp other then Possible CTT else
            let msg = Printf.sprintf "→ (Cau) is only transparently enforceable when the side not used for enforcement (%s) is SRP" (Tformula.to_string other) in
            error_tr msg
        in
        disj (conj (types_transparent Sup f) (srp_of_other_side g)) (conj (types_transparent Cau g) (srp_of_other_side f))
      (* (a IFF b):Cau <==> ((a IMP b) AND (b IMP a)):Cau -> thus IFF is typed analogously to AND:Cau and IMP:Cau *)
      | TIff (L, L, f, g) when srp g -> conj (types_transparent Sup f) (types_transparent Cau f)
      | TIff (L, L, _, _) -> error_tr "↔:L,L (Cau) is only transparently enforceable when the RHS is SRP" 
      | TIff (L, R, f, g) when (srp f && srp g) -> conj (types_transparent Sup f) (types_transparent Sup g) (* TODO: would a Possible verdict for types_transparent already imply SRP? *)
      | TIff (L, R, f, _) when (srp f) -> error_tr "↔:L,R (Cau) is only transparently enforceable when both sides are SRP, but the RHS is not SRP"
      | TIff (L, R, _, g) when (srp g) -> error_tr "↔:L,R (Cau) is only transparently enforceable when both sides are SRP, but the LHS is not SRP" 
      | TIff (L, R, _, _) -> error_tr "↔:L,R (Cau) is only transparently enforceable when both sides are SRP, but neither side is SRP"
      | TIff (R, L, f, g) when (srp f && srp g) -> conj (types_transparent Cau g) (types_transparent Cau f) (* TODO: would a Possible verdict for types_transparent already imply SRP? *)
      | TIff (R, L, f, _) when (srp f) -> error_tr "f ↔:R,L g (Cau) requires that f and g are SRP, but g is not"
      | TIff (R, L, _, g) when (srp g) -> error_tr "f ↔:R,L g (Cau) requires that f and g are SRP, but f is not"
      | TIff (R, L, _, _) -> error_tr "f ↔:R,L g (Cau) requires that f and g are SRP, but neither is SRP"
      | TIff (R, R, f, g) when srp f -> conj (types_transparent Cau g) (types_transparent Sup g)
      | TIff (R, R, _, _) -> error_tr "↔:R,R (Cau) LHS is not SRP"
      | TIff (_, _, f, g) ->
        let verdict_tr_f = if srp f then Possible CTT else error_tr "↔ (Cau) LHS is not SRP" in
        let verdict_tr_g = if srp g then Possible CTT else error_tr "↔ (Cau) RHS is not SRP" in
        conj
          (disj (conj (types_transparent Sup f) verdict_tr_g) (conj (types_transparent Cau f) verdict_tr_f))
          (disj (conj (types_transparent Cau f) verdict_tr_g) (conj (types_transparent Sup g) verdict_tr_f))
      (* Exists follows the same rule as the non-transparent case *)
      | TExists (_, f) -> types_transparent Cau f
      (* Forall follows the same rule(s) as the non-transparent case *)
      | TForall (x, f) when is_past_guarded s x false f -> types_transparent Cau f
      | TForall (x, _) -> error ("for causability " ^ x ^ " must be past-guarded")
      (* Next follows the same rule(s) as the non-transparent case *)
      | TNext (i, f) when Interval.equal i Interval.full -> types_transparent Cau f
      | TNext _ -> error "○ with non-[0,∞) interval is never Cau"
      | TSince (_, i, f, g) when Interval.has_zero i && srp f && srp g -> types_transparent Cau g
      | TSince (_, i, f, _) when Interval.has_zero i && srp f -> error_tr "f S[a,b) g requires that f and g are SRP, but g is not"
      | TSince (_, i, _, g) when Interval.has_zero i && srp g -> error_tr "f S[a,b) g requires that f and g are SRP, but f is not"
      | TSince (_, i, _, _) when Interval.has_zero i -> error_tr "f S[a,b) g requires that f and g are SRP, but neither is SRP"
      | TOnce (i, g) when Interval.has_zero i && srp g -> types_transparent Cau g
      | TOnce (i, _) when Interval.has_zero i -> error_tr "⧫[a,b) g is only transparently enforceable when g is SRP"
      | TOnce _ | TSince _ -> error "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      (* Eventually:Cau and Always:Cau should be unaffected by the transparency requirements *)
      | TEventually (_, f) | TAlways (_, f) -> types_transparent Cau f
      (* Until:LR (Cau) stays the same *)
      | TUntil (_, U _, _, _) -> error_tr "U[a,b):LR is only transparently enforceable when b≠∞"
      | TUntil (LR, _, f, g) -> conj (types_transparent Cau f) (types_transparent Cau g)
      | TUntil (_, i, f, g) when Interval.has_zero i && srp f -> types_transparent Cau g
      | TUntil (R, i, _, _) when Interval.has_zero i -> error_tr "f U[a,b):R g requires that f is SRP"
      | TUntil (_, _, f, g) -> conj (types_transparent Cau f) (types_transparent Cau g)
      | TPrev _ -> error "● is never Cau"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Sup -> 
    begin
      match f.f with
      | TFF -> Possible CTT
      | TPredicate (e, _, _) -> types_predicate pols Sup e
      | TNeg f -> types_transparent Cau f
      | TAnd (L, fs) when List.for_all (List.drop fs 1) ~f:srp -> types_transparent Sup (List.hd_exn fs)
      | TAnd (L, _) -> error_tr "∧:L (f::fs) (Sup) is only transparently enforceable when all formulas fs are SRP, but at least one of them is not"
      | TAnd (R, fs) when List.for_all (List.drop_last_exn fs) ~f:srp -> types_transparent Sup (List.last_exn fs)
      | TAnd (R, _) -> error_tr "∧:R [f1,...,fn-1,fn] (Sup) requires that all formulas [f1,...,fn-1] are SRP, but at least one of them is not"
      | TAnd (_, fs) ->
        let are_others_srp = Util.lists_with_one_removed fs |> List.map ~f:(List.for_all ~f:srp) in
        let is_srp_to_verdict  f = function
          | true -> Possible CTT
          | false ->
            let msg = Printf.sprintf "∧ [f0,...,fn] (Sup) requires all formulas besides the one used for enforcement (%s) are SRP, but at least one of them is not" (Tformula.to_string f) in
            error_tr msg
        in
        let types_and_srp f is_srp = conj (types_transparent Sup f) (is_srp_to_verdict f is_srp) in
        let vs = (List.map2_exn fs are_others_srp ~f:types_and_srp) in
        Constraints.disj' vs
      | TOr (_, fs) -> Constraints.conj' (List.map fs ~f:(types_transparent Sup))
      | TImp (_, f, g) -> conj (types_transparent Cau f) (types_transparent Sup g)
      | TIff (L, _, f, g) when srp f && srp g -> conj (types_transparent Cau f) (types_transparent Sup g) (* TODO: would a Possible verdict for types_transparent already imply SRP? *)
      | TIff (L, _, f, _) when (srp f) -> error_tr "f ↔:L,_ g (Sup) requires both f and g to be SRP, but the g is not" 
      | TIff (L, _, _, g) when (srp g) -> error_tr "f ↔:L,_ g (Sup) requires both f and g to be SRP, but the f is not" 
      | TIff (L, _, _, _) -> error_tr "f ↔:L,_ g (Sup) requires f and g to be SRP, but neither is SRP"
      | TIff (R, _, f, g) when srp f && srp g -> conj (types_transparent Sup f) (types_transparent Cau g) (* TODO: would a Possible verdict for types_transparent already imply SRP? *)
      | TIff (R, _, f, _) when (srp f) -> error_tr "f ↔:R,_ g (Sup) requires both f and g to be SRP, but g is not"
      | TIff (R, _, _, g) when (srp g) -> error_tr "f ↔:R,_ g (Sup) requires both f and g to be SRP, but f is not"
      | TIff (R, _, _, _) -> error_tr "f ↔:R,_ g (Sup) requires both f and g to be SRP, but neither is SRP"
      | TIff (_, _, f, g) ->
        let verdict_tr_f = if srp f then Possible CTT else error_tr "↔ (Cau) LHS is not SRP" in
        let verdict_tr_g = if srp g then Possible CTT else error_tr "↔ (Cau) RHS is not SRP" in
        disj
          (conj (conj (types_transparent Cau f) verdict_tr_g) (conj (types_transparent Sup g) verdict_tr_f))
          (conj (conj (types_transparent Sup f) verdict_tr_g) (conj (types_transparent Cau g) verdict_tr_f))
      | TExists (x, f) when is_past_guarded s x true f -> types_transparent Sup f
      | TExists (x, _) -> error ("for suppressability " ^ x ^ " must be past-guarded")
      | TForall (_, f) -> types_transparent Sup f
      | TNext (_, f) -> types_transparent Sup f
      | THistorically (i, f) when Interval.has_zero i && srp f -> types_transparent Sup f
      | THistorically (i, _) when Interval.has_zero i -> error_tr "■[a,b) f (Sup) requires f to be SRP"
      | THistorically _ -> error "■[a,b) with a > 0 is never Sup"
      | TSince (_, i, f, g) when not (Interval.has_zero i) && srp f && srp g -> types_transparent Sup f
      | TSince (_, _, f, g) when srp f && srp g -> conj (types_transparent Sup f) (types_transparent Sup g)
      | TSince (_, _, f, _) when srp f -> error_tr "f S[a,b) g (Sup) requires both f and g to be SRP, but g is not"
      | TSince (_, _, _, g) when srp g -> error_tr "f S[a,b) g (Sup) requires both f and g to be SRP, but f is not"
      | TSince (_, _, _, _) -> error_tr "f S[a,b) g (Sup) requires both f and g to be SRP, but both are not"
      | TEventually (_, f) when srp f -> types_transparent Sup f
      | TEventually (_, _) -> error_tr "◇f (Sup) requires f to be SRP"
      | TAlways (B _, f) -> types_transparent Sup f
      | TAlways _ -> error_tr "□[a,b) f (Sup) requires b≠∞"
      | TUntil (_, _, f, g) when srp f -> types_transparent Sup g
      | TUntil (_, _, _, _) -> error_tr "f U[a,b) g (Sup) requires f to be SRP"
      | TPrev _ -> error "● is never Sup"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Obs -> Possible CTT
  | _ -> Impossible (EFormula (None, f, t))

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
        match form.f with
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
        match form.f with
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
  match f with Some f -> Some Eformula.{ f ; enftype; id = 0; positions = form.positions } | None -> None

let convert_enforceable s pols (f: Tformula.t) b pos: Eformula.t =
  if not (Map.is_empty (Tformula.fv (Map.empty (module String)) f)) then
    let err_msg =
      Printf.sprintf "formula %s is not closed" (Tformula.to_string f) in
    Util.enf_error err_msg (Some pos)
  else ();
  match types s pols Cau f with (* TODO: check if policy constraints are necessary (and how to get them) *)
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

let convert_transparently_enforceable s pols (f: Tformula.t) b pos =
  let f' = convert_enforceable s pols f b pos in
  if Eformula.is_transparent f' then
    f'
  else
    let err_msg = Printf.sprintf "The formula\n %s\nis not transparently enforceable."
                     (Tformula.to_string f) in
    Util.enf_error err_msg (Some pos)

let epattern_of_tpattern tevents = function
  | TPPresent -> EPPresent
  | TPEventually i -> EPEventually i
  | TPAlways i -> EPAlways i
  | TPUntil (i, f) -> EPUntil (i, Eformula.of_tformula tevents f)
  | TPOnce i -> EPOnce i
  | TPHistorically i -> EPHistorically i
  | TPSince (i, f) -> EPSince (i, Eformula.of_tformula tevents f)

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
    | TCDefinition (_, _, _, _, _, _, _, {f=Tformula.TPredicate (name, _, _); _}) -> [name]
    | TCDefinition _ -> assert false
    | TCDefinitionDis (disjuncts, {f=Tformula.TPredicate (name, _, _); _}) ->
      let positions = Map.map disjuncts ~f:(fun d -> d.rule_pos) |> Map.data in
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
  let use_formula f = match f.f with
    | TPredicate (name, _, _) -> (match Map.find events name with
      | Some (_, _, Lex.TItl, _) -> [name]
      | _ -> [])
    | _ -> []
  in
  let use_formulas (fs: Tformula.t list) = List.concat_map fs ~f:use_formula in
  let use_pattern = function
    | TPPresent
    | TPEventually _
    | TPAlways _
    | TPOnce _
    | TPHistorically _ -> []
    | TPUntil (_, f)
    | TPSince (_, f) -> use_formula f
  in
  let use_pformulas ({fs; p}: tpformula) = use_formulas fs @ use_pattern p in
  let use_disjunct (d: tdisjunct) = use_pformulas d.pf @ use_formulas (d.exceptions@d.scopes@d.var_renaming) in
  let use_disjuncts disjuncts = Map.map disjuncts ~f:use_disjunct |> Map.data |> List.concat in
  let aux = function
    | TCImplication (_, _, _, pf1, exceptions, scopes, pf2, _, _) ->
       use_pformulas pf1 @ use_pformulas pf2 @ use_formulas (exceptions@scopes) |> List.dedup_and_sort ~compare:String.compare
    | TCDefinition (_, _, _, pf, exceptions, scopes, _, _) ->
      use_pformulas pf @ use_formulas (exceptions@scopes) |> List.dedup_and_sort ~compare:String.compare
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

let get_types_fun = function
  | Some (itvs, stricts) -> types_transparent itvs stricts
  | None -> types

let type_tformulas s pols itl_srp (fs: Tformula.t list) t =
  let types_fun = get_types_fun itl_srp in
  match t with
  | Cau ->
    List.map fs ~f:(types_fun s pols t)
    |> List.fold ~f:conj ~init:(Possible CTT)
  | Sup ->
    begin match itl_srp with
    | Some (itvls, stricts) -> (* transparency requires that other formulas are SRP *)
      let srp = strictly_relative_past ~itl_itvs_and_strict:(itvls, stricts) in
      let are_others_srp = Util.lists_with_one_removed fs |> List.map ~f:(List.for_all ~f:srp) in
      let is_srp_to_verdict f = function
        | true -> Possible CTT
        | false ->
          let msg = Printf.sprintf "the conjunction of exception predicates is transparently enforceable when all predicates besides the one used for enforcement (%s) are SRP, but at least one of them is not SRP" (Tformula.to_string f) in
          Impossible (EFormulasTransparent (Some ("AND", msg), fs, t))
      in
      let types_and_srp f srp = conj (types_fun s pols t f) (is_srp_to_verdict f srp) in
      let vs = List.map2_exn fs are_others_srp ~f:types_and_srp in
      Constraints.disj' vs
    | None -> disj' (List.map fs ~f:(types_fun s pols t))
    end
  | _ -> assert false

let type_tpformula itl_srp (s:Tlex.tprog) (pos: Lexing.position) pols enftype (tpf: tpformula) : verdict =
  let types_fun = get_types_fun itl_srp in
  match enftype with
  | Cau ->
    begin match tpf.p with
    | TPPresent -> type_tformulas s pols itl_srp tpf.fs Cau
    | TPEventually _ -> type_tformulas s pols itl_srp tpf.fs Cau
    | TPAlways _ -> type_tformulas s pols itl_srp tpf.fs Cau
    | TPUntil (i, _) when Interval.is_bounded i -> type_tformulas s pols itl_srp tpf.fs Cau
    | TPUntil _ -> Impossible (EPattern (pos, "can only be made \"Cau\" if the interval is bounded", tpf, enftype))
    | TPOnce i when Interval.has_zero i -> type_tformulas s pols itl_srp tpf.fs Cau
    | TPOnce _ -> Impossible (EPattern (pos, "can only be made \"Cau\" if zero is in the interval", tpf, enftype))
    | TPHistorically _ -> Impossible (EPattern (pos, "can never be made \"Cau\"", tpf, enftype))
    | TPSince (i, g) when Interval.has_zero i -> types_fun s pols Cau g
    | TPSince _ -> Impossible (EPattern (pos, "can only be made \"Cau\" if zero is in the interval", tpf, enftype))
    end
  | Sup ->
    begin match tpf.p with
    | TPPresent -> type_tformulas s pols itl_srp tpf.fs Sup
    | TPEventually _ -> type_tformulas s pols itl_srp tpf.fs Sup
    | TPAlways _ -> type_tformulas s pols itl_srp tpf.fs Sup
    | TPUntil _ -> type_tformulas s pols itl_srp tpf.fs Sup
    | TPOnce _ -> Impossible (EPattern (pos, "can never be made \"Sup\"", tpf, enftype))
    | TPHistorically _ -> type_tformulas s pols itl_srp tpf.fs Sup
    | TPSince (i, g) when Interval.has_zero i -> type_tformulas s pols itl_srp tpf.fs Sup |> conj (types_fun s pols Cau g)
    | TPSince _ -> type_tformulas s pols itl_srp tpf.fs Sup (* when not (Interval.has_zero i) *)
    end
  | Obs -> Possible CTT
  | _ -> Impossible (EPattern (pos, "can only be made \"Cau\", \"Sup\", or \"Obs\"", tpf, enftype))

let get_exception_predicates ?(negated=false) (s: Tlex.tprog) rule_idx =
  let exception_idxs = Map.find_multi s.rule_tree.exceptions rule_idx in
  let exception_predicates = List.map exception_idxs ~f:(try Map.find_exn s.exception_predicates with _ -> assert false) in
  if negated then
    List.map exception_predicates ~f:(fun x -> Tformula.tneg x.positions x)
  else exception_predicates

let get_scope_predicates (s: Tlex.tprog) rule_idx = 
  let scope_idxs = Map.find_multi s.rule_tree.scopes rule_idx in
  List.map scope_idxs ~f:(try Map.find_exn s.scope_predicates with _ -> assert false)

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

let type_exceptions itl_srp s pols exceptions =
  let exceptions_neg = List.map exceptions ~f:(fun f -> Tformula.tneg f.positions f) in
  type_tformulas s pols itl_srp exceptions_neg Cau (* TODO: is Cau correct here? *)

let type_scopes itl_srp s pols scopes =
  type_tformulas s pols itl_srp scopes Sup (* TODO: is Sup correct here? *)

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

let var_is_past_guarded_in_rule rule var positions =
  match rule with
  | TCImplication (_, _, pos, pf1, exceptions, scopes, pf2, _, _) ->
    assert false
  | _ -> assert false

let free_variables_tc_implication_are_past_guarded = function
  | TCImplication (_, _, pos, pf1, exceptions, scopes, pf2, _, _) as rule ->
    let free_vars = Map.empty (module String) in
    let free_vars = fv_of_tpformulas free_vars pf1 in
    let free_vars = fv_of_tpformulas free_vars pf2 in
    let free_vars = fv_of_tformulas free_vars exceptions in
    let free_vars = fv_of_tformulas free_vars scopes in
    Map.iteri free_vars ~f:(fun ~key:var ~data:positions -> var_is_past_guarded_in_rule rule var positions)
  | _ -> assert false

let type_trule_compilation itl_itvs_and_stricts (s:Tlex.tprog) ((verdict, pg_map): verdict * pg_map) rule: verdict * pg_map =
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
    | TCImplication (_, _, pos, pf1, exceptions, scopes, pf2, rt, rcs) ->
      (* TODO: check past-guardedness of all free variables in this rule, should be the same for transparantly enforceable and enforceable *)
      begin match rt with
        | Vanilla ->
          vanilla_rule_constraints_warning pos rcs;
          verdict, pg_map (* do not aadd any typing constraints in regards to this rule *)
        | Enforceable ->
          free_variables_tc_implication_are_past_guarded rule;
          let pols, suppress_indices, suppress_conditions, cause_effects, suppress_scopes, cause_exceptions =
            parse_rule_constraints pos pols (List.length pf1.fs) rcs
          in
          let verdict_exceptions =
            if cause_exceptions then type_exceptions None s pols exceptions
            else Impossible (ERule (pos, "exceptions are not marked as causing"))
          in
          let verdict_scopes =
            if suppress_scopes then type_scopes None s pols scopes
            else Impossible (ERule (pos, "scopes are not marked as suppressing"))
          in
          let verdict_references = disj verdict_exceptions verdict_scopes in
          let verdict_conditions =
            if suppress_conditions then
              type_tpformula None s pos pols Sup pf1
              |> disj verdict_references
            else
              match suppress_indices with
                | Some indices ->
                  let pf1' = { pf1 with fs = List.filteri pf1.fs ~f:(fun i _ -> List.mem indices i ~equal:Int.equal) } in
                  (* let f1_filtered = List.filteri f1 ~f:(fun i _ -> List.mem indices i ~equal:Int.equal) in *)
                  type_tpformula None s pos pols Sup pf1'
                | None ->
                  Impossible (ERule (pos, "no conditions are marked as suppressing"))
          in
          let verdict_effects =
            if cause_effects then type_tpformula None s pos pols Cau pf2
            else Impossible (ERule (pos, "effects are not marked as causing"))
          in
          let verdict_rule_implication = disj verdict_conditions verdict_effects |> conj verdict in
          begin match verdict_rule_implication with
            | Possible _ -> verdict_rule_implication, pg_map
            | Impossible e ->
              let err_msg = Printf.sprintf "Impossible, rule is not enforceable: %s" (Errors.to_string e) in
              Util.enf_error err_msg (Some pos)
          end
        | Transparent ->
          let tr = Some (itl_itvs_and_stricts) in
          let pols, suppress_indices, suppress_conditions, cause_effects, suppress_scopes, cause_exceptions =
            parse_rule_constraints pos pols (List.length pf1.fs) rcs
          in
          let srp = strictly_relative_past ~itl_itvs_and_strict:itl_itvs_and_stricts in
          let srp_exceptions = List.for_all exceptions ~f:srp in
          let srp_scopes = List.for_all scopes ~f:srp in
          let srp_conditions = srp_of_tpformula itl_itvs_and_stricts pf1 in
          let srp_effects = srp_of_tpformula itl_itvs_and_stricts pf2 in
          let verdict_exceptions =
            if cause_exceptions then
              if srp_scopes && srp_conditions && srp_effects then
                type_exceptions None s pols exceptions
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
                type_scopes None s pols scopes
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
                type_tpformula tr s pos pols Sup pf1
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
                  let pf1_used = { pf1 with fs = List.filteri pf1.fs ~f:(fun i _ -> List.mem indices i ~equal:Int.equal) } in
                  let pf1_unused = { pf1 with fs = List.filteri pf1.fs ~f:(fun i _ -> List.mem indices i ~equal:(fun x y -> Int.equal x y |> not)) } in
                  let srp_conditions_unused = srp_of_tpformula itl_itvs_and_stricts pf1_unused in
                  if srp_conditions_unused && srp_exceptions && srp_scopes && srp_effects then
                    type_tpformula tr s pos pols Sup pf1_used
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
                type_tpformula tr s pos pols Cau pf2
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
            | Possible _ -> verdict_rule_implication, pg_map
            | Impossible e ->
              let err_msg = Printf.sprintf "Impossible, rule is not transparently enforceable: %s" (Errors.to_string e) in
              Util.enf_error err_msg (Some pos)
          end
      end
    | TCDefinition (idx, _, _, pf1, ex, sc, _, f2) ->
      let e = get_predicate_name f2 in
      let pos = try snd (Map.find_exn s.rule_tree.label_of_rule idx) with _ -> assert false in
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
        let v_ex = type_exceptions itl_srp s pols_tr ex in
        let v_sc = type_scopes itl_srp s pols_tr sc in
        let v_pf1 = type_tpformula itl_srp s pos pols_tr t pf1 in
        match t with
        | Cau -> (* all parts of the definition must be Cau *)
          let verdict_references = conj v_ex v_sc in
          conj (conj v_pf1 verdict_references) verdict
        | Sup -> (* only one part of the definition must be Sup *)
          let verdict_references = disj v_ex v_sc in
          conj (disj v_pf1 verdict_references) verdict
        | Obs -> verdict
        | _ -> assert false
      in
      let verdicts = List.map dnf_of_v ~f:aux in
      Constraints.disj' verdicts, pg_map
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
        let type_disjunct (d: tdisjunct) =
          let pf' = { d.pf with fs = d.pf.fs @ d.var_renaming } in (* combine renaming conditions with the actual conditions of the constitutive rule *)
          (* let ex_neg = List.map d.exceptions ~f:(fun f -> Tformula.tneg f.positions f) in *)
          (* let v_ex = type_tpformula itl_srp s d.rule_pos pols_tr t ex_neg TPPresent in
          let v_sc = type_tpformula itl_srp s d.rule_pos pols_tr t d.scopes TPPresent in *)
          let v_ex = type_exceptions itl_srp s pols_tr d.exceptions in
          let v_sc = type_scopes itl_srp s pols_tr d.scopes in
          let v_pf' = type_tpformula itl_srp s d.rule_pos pols_tr t pf' in
          begin match t with
            | Cau -> (* all parts of the definition must be Cau *)
              let verdict_references = conj v_ex v_sc in
              conj (conj v_pf' verdict_references) verdict
            | Sup -> (* only one part of the definition must be Sup *)
              let verdict_references = disj v_ex v_sc in
              conj (disj v_pf' verdict_references) verdict
            | Obs -> verdict
            | _ -> assert false
          end
        in
        Map.map disjuncts ~f:type_disjunct
        |> Map.data
        |> Constraints.disj'
        |> conj verdict
      in
      let verdicts = List.map dnf_of_v ~f:aux in
      Constraints.disj' verdicts, pg_map

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

let relative_interval_of_disjunct itl_itvs (d: tdisjunct) =
  (* The relative interval of the "variable renaming conditions" will always be 0 and is thus ignored *)
  let conditions_itv = relative_interval_of_tpformula itl_itvs d.pf in
  let exceptions_itv = relative_interval_of_tformulas itl_itvs d.exceptions in
  let scopes_itv = relative_interval_of_tformulas itl_itvs d.scopes in
  Zinterval.lub conditions_itv exceptions_itv |> Zinterval.lub scopes_itv

let relative_interval_itl itl_itvs = function
  (* requires that all relative intervals of events used in the given rule have already been computed *)
  | TCDefinition (_, _, _, pf, e, s, _, {f=Tformula.TPredicate (name, _, _); _}) ->
    let conditions_itv = relative_interval_of_tpformula itl_itvs pf in
    let exceptions_itv = relative_interval_of_tformulas itl_itvs e in
    let scopes_itv = relative_interval_of_tformulas itl_itvs s in
    let itv = Zinterval.lub conditions_itv exceptions_itv |> Zinterval.lub scopes_itv in
    Map.add_exn itl_itvs ~key:name ~data:itv
  | TCDefinition _ -> assert false (* final formula must be a predicate *)
  | TCDefinitionDis (disjuncts, {f=Tformula.TPredicate (name, _, _); _}) ->
    let relative_itvs_disjuncts = List.map (Map.data disjuncts) ~f:(relative_interval_of_disjunct itl_itvs) in
    let itv = List.fold relative_itvs_disjuncts ~init:Zinterval.full ~f:Zinterval.lub in
    Map.add_exn itl_itvs ~key:name ~data:itv
  | TCDefinitionDis _ -> assert false (* final formula must be a predicate *)
  | _ -> itl_itvs


(* let strict_of_disjunct itl_strict (_, _, _, f, p, e, s, _) = *)
let strict_of_disjunct itl_strict (d: tdisjunct) =
  (* The "variable renaming conditions" will always be strict and are thus ignored *)
  let conditions_strict = strict_of_tpformula itl_strict d.pf in
  let exceptions_strict = strict_of_tformulas itl_strict d.exceptions in
  let scopes_itv = strict_of_tformulas itl_strict d.scopes in
  conditions_strict && exceptions_strict && scopes_itv

let strict_itl itl_strict = function
  (* requires that all "strictness"-constraints of events used in the given rule have already been computed *)
  | TCDefinition (_, _, _, pf, e, s, _, {f=Tformula.TPredicate (name, _, _); _}) ->
    let conditions_strict = strict_of_tpformula itl_strict pf in
    let exceptions_strict = strict_of_tformulas itl_strict e in
    let scopes_itv = strict_of_tformulas itl_strict s in
    let is_strict = conditions_strict && exceptions_strict && scopes_itv in
    Map.add_exn itl_strict ~key:name ~data:is_strict
  | TCDefinition _ -> assert false
  | TCDefinitionDis (disjuncts, {f=Tformula.TPredicate (name, _, _); _}) ->
    let is_strict = List.for_all (Map.data disjuncts) ~f:(strict_of_disjunct itl_strict) in
    Map.add_exn itl_strict ~key:name ~data:is_strict
  | TCDefinitionDis _ -> assert false
  | _ -> itl_strict

(* TODO: implement past guardedness check *)
(* let rule_is_past_guarded (pg, itl_pg) = function *)
let rule_is_past_guarded _ = function
  | _ ->
  (* | TCImplication (_, _, pos, f1, p, ex, sc, f2, q, rt, rcs) ->
    let pf = formulas_from_tpattern p in
    let qf = formulas_from_tpattern q in
    let fvs = List.fold (f1@ex@sc@f2@pf@qf) ~init:(Map.empty (module String)) ~f:Tformula.fv
    in *)
    assert false
  (* | TCDefinition _ -> assert false
  | TCDefinitionDis _ -> assert false *)

let rules_are_past_guarded rules =
  List.fold rules ~init:(true, Map.empty (module String)) ~f:rule_is_past_guarded
  |> ignore

let type_trules_compilation (tprog:Tlex.tprog) (compilation_rules: (int, trule_compilation, 'a) Map.t) : ((string, EnfType.t * bool, 'b) Map.t * int list) =
  let def_internal = def_sets compilation_rules tprog.tevents in
  let use_internal = use_sets compilation_rules tprog.tevents in
  check_used_events_are_defined tprog def_internal use_internal;
  let sorted_rule_indices = topological_sort (Map.keys compilation_rules) def_internal use_internal in
  let compilation_rules_sorted = List.map sorted_rule_indices ~f:(fun idx -> Map.find_exn compilation_rules idx) in
  (* TODO: check past-guardedness of rules *)
  rules_are_past_guarded compilation_rules_sorted;
  let itl_itvs = List.fold (List.rev compilation_rules_sorted) ~f:relative_interval_itl ~init:(Map.empty (module String)) in
  let itl_strict = List.fold (List.rev compilation_rules_sorted) ~f:strict_itl ~init:(Map.empty (module String)) in
  let verdict, pg_map = List.fold compilation_rules_sorted ~f:(type_trule_compilation (itl_itvs, itl_strict) tprog) ~init:(Possible CTT, Map.empty (module String)) in
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

let collect_constitutive_rules (tprog: Tlex.tprog) : (Lexing.position * int * trule * Tformula.t list * Tformula.t list) list =
(* let collect_constitutive_rules (tprog: Tlex.tprog) = *)
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

(* let combine_constitutive_rules (rules: (Lexing.position * int * trule * Tformula.t list * Tformula.t list) list) : trule_compilation list = *)
let combine_constitutive_rules rules: trule_compilation list =
  let collect_and_separate_event_definitions m (pos, idx, rule, exceptions, scopes) =
    let trule_type = match rule with
      | TConstitutive _ -> TRTConstitutive
      | TExceptionC _ -> TRTExceptionC
      | _ -> assert false
    in
    let separate_event_definitions pf (m': (string, 'a, 'b) Map.t) f = match f.f with
      | Tformula.TPredicate (name, terms, _) ->
        let disjunct: tdisjunct =
          { rule_id = idx;
            tt = trule_type;
            rule_pos = pos;
            def_positions = f.positions;
            pf = pf;
            exceptions = exceptions;
            scopes = scopes;
            var_original = terms;
            var_renaming = [] (* dummy value, computed in a next step *)
          }
        in
        Map.add_multi m' ~key:name ~data:disjunct
      | _ -> assert false
    in
    match rule with
    | TConstitutive (_, pf1, f2)
    | TExceptionC (_, pf1, _, _, f2) ->
      List.fold f2 ~init:m ~f:(separate_event_definitions pf1)
    | _ -> assert false
  in
  let event_def_map = List.fold rules ~init:(Map.empty (module String)) ~f:collect_and_separate_event_definitions in
  (* let replace_variables (idx, trule_type, pos, f1, exceptions, scopes, p, terms) = *)
  let replace_variables (d: tdisjunct): tdisjunct =
    let rename_fun (ts,i) t =
      let t = TTerm.
        { trm=TVar ("__t" ^ string_of_int i); (* TODO: reserve variable names starting with '__t' as internal *)
          tt=t.tt;
          positions=[] (* don't attribute any physical locations with these internal 'renamed' paremeters *)
        }
      in
      t::ts, i+1
    in
    let var_renamed = List.fold d.var_original ~init:([],0) ~f:rename_fun
                      |> fst in
    let term_conditions = List.map2_exn d.var_original var_renamed ~f:(fun t1 t2 -> Tformula.teqconst [] t1 t2) in
    { d with var_renaming = term_conditions }
  in
  let event_map_renamed = Map.map event_def_map ~f:(List.map ~f:replace_variables) in
  let extract_terms (d: tdisjunct) : Tformula.TTerm.t list = d.var_original in
  let to_tr_def_dis ((name, definitions): (string * 'defs)) =
    let add_disjunct_to_map (m, k) (d: tdisjunct) =
      Map.add_exn m ~key:k ~data:d, k+1
    in
    let disjunction = List.fold definitions
                        ~init:(Map.empty (module Int), 0)
                        ~f:add_disjunct_to_map
                      |> fst
    in
    let terms = Map.find_exn event_map_renamed name
                |> List.hd_exn
                |> extract_terms in
    let positions: (string, Lexing.position list, 'string_comp) Map.t =
      let aux (d: tdisjunct) = d.def_positions in
      Map.map event_map_renamed ~f:(List.concat_map ~f:aux)
    in
    TCDefinitionDis (disjunction, Tformula.tpredicate (Map.find_exn positions name) name terms Lex.Predicate)
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
        | TScope (_, pf1, r, f2)
          -> Some (TCDefinition (idx, TRTScope, pos, pf1, exceptions, scopes, r, f2))
        | TException (_, pf1, r, f2)
          -> Some (TCDefinition (idx, TRTException, pos, pf1, exceptions, scopes, r, f2))
        | TExceptionC (_, pf1, r, f2, _)
          -> Some (TCDefinition (idx, TRTExceptionC, pos, pf1, exceptions, scopes, r, f2))
        | _ -> None
      end
    | _ -> None)

let create_imp_rules tprog =
  List.filter_map tprog.tstmts ~f:(function
    | TSRule (pos, idx, _, _, trule, _) ->
      let ex = get_exception_predicates ~negated:true tprog idx in
      let sc = get_scope_predicates tprog idx in
      begin match trule with
        | TObligation (_, pf1, pf2, rt, rcs)
          -> Some (TCImplication (idx, TRTObligation, pos, pf1, ex, sc, pf2, rt, rcs))
        | TPermission (_, pf1, pf2, rt, rcs)
          -> Some (TCImplication (idx, TRTPermission, pos, pf1, ex, sc, pf2, rt, rcs))
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

let convert_tformulas (s: tprog) (enftype: EnfType.t) pols b (fs: Tformula.t list) : Eformula.t list =
  let pols' = Map.map pols ~f:fst in
  let convert enftype f =
    convert s pols' b enftype f
    |> Option.value_exn (* If conversion fails, then the enforcement type checking is wrong *)
  in
  match enftype with
  | Cau -> List.map fs ~f:(convert Cau)
  | Sup -> 
    let find_first_possible _ f =
      match types s pols Sup f with
      | Possible _ -> true
      | Impossible _ -> false
    in
    let idx = List.findi_exn ~f:find_first_possible fs |> fst in (* there must exist at least one formula which types correctly, otherwise the enforcement checking is wrong *)
    let aux i f = if i = idx then convert Sup f else Eformula.of_tformula pols f in
    List.mapi fs ~f:aux
  | Obs -> List.map fs ~f:(convert Obs)
  | _ -> assert false

let convert_tpformula (s: tprog) (enftype: EnfType.t) pols b (tpf: tpformula) : epformula =
  match enftype with
  | Cau ->
    begin match tpf.p with
      | TPPresent -> { fs = convert_tformulas s Cau pols b tpf.fs; p = EPPresent }
      (* | TPEventually i -> assert false *)
      (* | TPAlways i -> assert false *)
      (* | TPUntil (i, g) -> assert false *)
      (* | TPOnce i -> assert false *)
      (* | TPHistorically i -> assert false *)
      (* | TPSince (i, g) -> assert false *)
      | _ -> assert false
    end
  | Sup ->
    begin match tpf.p with
      | TPPresent -> { fs = convert_tformulas s Sup pols b tpf.fs; p = EPPresent }
      (* | TPEventually i -> assert false *)
      (* | TPAlways i -> assert false *)
      (* | TPUntil (i, g) -> assert false *)
      (* | TPOnce i -> assert false *)
      (* | TPHistorically i -> assert false *)
      (* | TPSince (i, g) -> assert false *)
      | _ -> assert false
    end
  | Obs -> 
    begin match tpf.p with
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


let  merge_used_and_unused indices_used used unused =
  let n = List.length used + List.length unused in
  let all_indices = List.init n ~f:(fun i -> i) in
  let unused_indices = List.filter all_indices ~f:(fun i -> not (List.mem indices_used i ~equal:Int.equal)) in
  let merge i = 
    let aux j _ = i=j in
    match List.findi indices_used ~f:aux with
      | Some (_, idx) -> List.nth_exn used idx
      | None ->
        let idx = List.findi_exn unused_indices ~f:aux |> snd in
        List.nth_exn unused idx
    in
  List.init n ~f:merge

let epformula_of_tpformula tevents (tpf: tpformula): epformula =
  {
    fs = List.map tpf.fs ~f:(Eformula.of_tformula tevents);
    p = epattern_of_tpattern tevents tpf.p
  }

(* let convert_compilation_rule (s: tprog) pols b = function *)
let convert_compilation_rule (s: tprog) pols _ = function
  | TCImplication (idx, trt, pos, tpf1, ex, sc, tpf2, rt, rcs) ->
    begin match rt with
      | Vanilla ->
        let ert = erule_type_from_trule_type trt in
        let ex' = List.map ex ~f:(Eformula.of_tformula pols) in
        let sc' = List.map sc ~f:(Eformula.of_tformula pols) in
        let epf1 = epformula_of_tpformula s.tevents tpf1 in
        let epf2 = epformula_of_tpformula s.tevents tpf2 in
        ECImplication (idx, ert, pos, epf1, ex', sc', epf2, rt, rcs)
      | Enforceable ->
        (* TODO: interpret rule constraints (again)
            -> find first applicable way of making the implication Cau
            -> convert based on that
        *)
        (* let pols, suppress_indices, suppress_conditions, cause_effects, suppress_scopes, cause_exceptions =
          parse_rule_constraints pos pols (List.length f1) rcs
        in
        begin match cause_exceptions, type_exceptions None s pos pols ex with
          | true, Possible constraints ->
            let pols' = solve constraints |> List.hd_exn in (* TODO: iterate through found policies *)
            let ert = erule_type_from_trule_type trt in
            let f1' = List.map f1 ~f:(Eformula.of_tformula pols) in
            let ex' =
              convert_pattern_with_formulas s Cau pols' b ex TPPresent
              |> fst
            in
            let sc' = List.map sc ~f:(Eformula.of_tformula pols) in
            let f2' = List.map f2 ~f:(Eformula.of_tformula pols) in
            let p' = epattern_of_tpattern s p in
            let q' = epattern_of_tpattern s q in
            ECImplication (idx, ert, pos, f1', p', ex', sc', f2', q', rt, rcs)
          | _ ->
            begin match suppress_scopes, type_scopes None s pos pols sc with
            | true, Possible constraints ->
              let pols' = solve constraints |> List.hd_exn in (* TODO: handle multiple/no options *)
              let ert = erule_type_from_trule_type trt in
              let f1' = List.map f1 ~f:(Eformula.of_tformula pols) in
              let ex' = List.map ex ~f:(Eformula.of_tformula pols) in
              let sc' =
                convert_pattern_with_formulas s Cau pols' b sc TPPresent
                |> fst
              in
              let f2' = List.map f2 ~f:(Eformula.of_tformula pols) in
              let p' = epattern_of_tpattern s p in
              let q' = epattern_of_tpattern s q in
              ECImplication (idx, ert, pos, f1', p', ex', sc', f2', q', rt, rcs)
            | _ ->
              begin match suppress_conditions, type_pattern_with_formulas None s pos pols Sup f1 p with
              | true, Possible constraints ->
                let pols' = solve constraints |> List.hd_exn in (* TODO: handle empty/multiple *)
                let ert = erule_type_from_trule_type trt in
                let f1', p' =
                  convert_pattern_with_formulas s Cau pols' b f1 p
                in
                let ex' = List.map ex ~f:(Eformula.of_tformula pols) in
                let sc' = List.map sc ~f:(Eformula.of_tformula pols) in
                let f2' = List.map f2 ~f:(Eformula.of_tformula pols) in
                let q' = epattern_of_tpattern s q in
                ECImplication (idx, ert, pos, f1', p', ex', sc', f2', q', rt, rcs)
              | _ ->
                let v = begin match suppress_indices with
                    | Some indices ->
                      let f1_filtered = List.filteri f1 ~f:(fun i _ -> List.mem indices i ~equal:Int.equal) in
                      type_pattern_with_formulas None s pos pols Sup f1_filtered p
                    | None -> 
                      Impossible (ERule (pos, "no conditions are marked as suppressing"))
                  end in
                begin match v with
                | Possible constraints ->
                  let indices = Option.value_exn suppress_indices in
                  let pols' = solve constraints |> List.hd_exn in (*TODO*)
                  let ert = erule_type_from_trule_type trt in
                  let f1_used = List.filteri f1 ~f:(fun i _ -> List.mem indices i ~equal:Int.equal) in
                  let f1_unused = List.filteri f1 ~f:(fun i _ -> List.mem indices i ~equal:(fun x y -> Int.equal x y |> not)) in
                  let f1_used', p' =
                    convert_pattern_with_formulas s Cau pols' b f1_used p
                  in
                  let f1_unused' = List.map f1_unused ~f:(Eformula.of_tformula pols) in
                  let f1' = merge_used_and_unused indices f1_used' f1_unused' in
                  let ex' = List.map ex ~f:(Eformula.of_tformula pols) in
                  let sc' = List.map sc ~f:(Eformula.of_tformula pols) in
                  let f2' = List.map f2 ~f:(Eformula.of_tformula pols) in
                  let q' = epattern_of_tpattern s q in
                  ECImplication (idx, ert, pos, f1', p', ex', sc', f2', q', rt, rcs)
                | _ ->
                  begin match cause_effects, type_pattern_with_formulas None s pos pols Cau f2 q with
                    | true, Possible constraints ->
                      let pols' = solve constraints |> List.hd_exn in (* TODO *)
                      let ert = erule_type_from_trule_type trt in
                      let f1' = List.map f1 ~f:(Eformula.of_tformula pols) in
                      let ex' = List.map ex ~f:(Eformula.of_tformula pols) in
                      let sc' = List.map sc ~f:(Eformula.of_tformula pols) in
                      let f2', q' =
                        convert_pattern_with_formulas s Cau pols' b f2 q
                      in
                      let p' = epattern_of_tpattern s p in
                      ECImplication (idx, ert, pos, f1', p', ex', sc', f2', q', rt, rcs)
                    | _ -> assert false (* TODO: test that this assertion cannot be triggered when enforcability typing succeeded previously *)
                  end
                end
              end
            end
          end *)
          assert false

      | Transparent ->
        (* TODO: interpret rule constraints (again)
            -> find first applicable way of making the implication Cau
            -> analogous to non-transparent, but requires SRP checks
            -> convert based on that
        *)
        assert false
    end
    (* let f1s, p_e = convert_pattern_with_formulas s Sup pols b [f1;exceptions;scopes] p in
    let f2s, q_e = convert_pattern_with_formulas s Cau pols b [f2] q in
    let f1_e, e_e, s_e = match f1s with
      | [f1;exceptions;scopes] -> f1, exceptions, scopes
      | _ -> assert false
    in
    let f2_e = match f2s with
      | [f2] -> f2
      | _ -> assert false
    in
    let ert = erule_type_from_trule_type trt in
    ECImplication (idx, ert, pos, f1_e, p_e, e_e, s_e, f2_e, q_e, rt, rcs) *)
  | TCDefinition _ ->
  (* | TCDefinition (idx, trt, pos, f1, p, exceptions, scopes, refs, f2) -> *)
    assert false
    (* let pred_name = match f2 with
      | Tformula.TPredicate (name, _, _) -> name
      | _ -> assert false
    in
    let enftype = match Map.find pols pred_name with
      | Some t -> t
      | None -> Obs
    in
    let f1s, p_e = convert_pattern_with_formulas s enftype pols b [f1;exceptions;scopes] p in
    let f1_e, e_e, s_e = match f1s with
      | [f1;exceptions;scopes] -> f1, exceptions, scopes
      | _ -> assert false
    in
    let f2_e = match convert s pols (C Lextime.Span.zero) enftype f2 with (* TODO what is the correct/expected value for the bound `b`? *)
      | Some f2_e -> f2_e
      | None -> Util.enf_error ("Internal predicate \"" ^ Tformula.to_string f2 ^ "\" cannot be converted.") None (* TODO, should this be replaced with assert false/ why might this happen, could it even happen after enforcement checking? *)
    in
    let ert = erule_type_from_trule_type trt in
    ECDefinition (idx, ert, pos, f1_e, p_e, e_e, s_e, refs, f2_e)  *)
  | TCDefinitionDis _ ->
  (* | TCDefinitionDis (disjuncts, g) -> *)
    assert false
    (* let pred_name = match g with
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
      let f1s, p_e = convert_pattern_with_formulas s enftype pols b [f1;exceptions;scopes;cs] p in
      let f1_e, e_e, s_e, cs_e = match f1s with
        | [f1;exceptions;scopes;cs] -> f1, exceptions, scopes, List.map cs ~f:snd
        | _ -> assert false
      in
      let ert = erule_type_from_trule_type trt in
      idx, ert, pos, f1_e, p_e, e_e, s_e, cs_e
    in
    let disjuncts_e = Map.map disjuncts ~f:convert_disjunct in
    ECDefinitionDis (disjuncts_e, g_e) *)

let convert_compilation_rules tprog pols b rules =
  Map.map rules ~f:(convert_compilation_rule tprog pols b)

let erules_from_compilation_rules (compilation_rules: (int, trule_compilation, Int.comparator_witness) Map.t) : (int, erule, Int.comparator_witness) Map.t =
  let c_rules = Map.to_alist compilation_rules in
  let aux erules (c_idx, c_rule) = match c_rule with
    | TCImplication (r_idx, trt, pos, _, _, _, _, _, _) ->
      begin match trt with
        | TRTObligation -> Map.add_exn erules ~key:r_idx ~data:(EObligation (pos, c_idx))
        | TRTPermission -> Map.add_exn erules ~key:r_idx ~data:(EPermission (pos, c_idx))
        | _ -> assert false
    end
    | TCDefinition (r_idx, trt, pos, _, _, _, _, _) ->
      begin match trt with
        | TRTException -> Map.add_exn erules ~key:r_idx ~data:(EException (pos, c_idx))
        | TRTExceptionC -> Map.update erules r_idx ~f:(function
            | Some (EExceptionC (pos, -1, constitutives)) -> EExceptionC (pos, c_idx, constitutives)
            | Some _ -> assert false (* not -1: exception cannot be defined already *)
            | None -> EExceptionC (pos, c_idx, []))
        | TRTScope -> Map.add_exn erules ~key:r_idx ~data:(EScope (pos, c_idx))
        | _ -> assert false
      end
    | TCDefinitionDis (disjunct_map, _) ->
      (* let add_disjuncts_to_map m (d_idx, (r_idx, trt, _, _, _, _, _, _)) = *)
      let add_disjuncts_to_map m (d_idx, disjunct) =
        let trt = disjunct.tt in
        let r_idx = disjunct.rule_id in
        let pos = disjunct.rule_pos in
        begin match trt with
          | TRTConstitutive ->
            Map.update m r_idx ~f:(function
              | Some (EConstitutive (pos, ds)) -> EConstitutive (pos, (c_idx, d_idx)::ds)
              | Some _ -> assert false
              | None -> EConstitutive (pos, [(c_idx, d_idx)]))
          | TRTExceptionC ->
            Map.update m r_idx ~f:(function
              | Some (EExceptionC (pos, c_idx_ex, constitutives)) -> EExceptionC (pos, c_idx_ex, (c_idx, d_idx)::constitutives)
              | Some _ -> assert false
              | None -> EExceptionC (pos, -1, [(c_idx, d_idx)]))
          | _ -> assert false
        end
      in
      Map.to_alist disjunct_map |> List.fold ~init:erules ~f:add_disjuncts_to_map
  in
  List.fold c_rules ~f:aux ~init:(Map.empty (module Int))

let do_type _ (tprog: Tlex.tprog) b : Elex.eprog =
  let compilation_rules  = create_compilation_rules tprog in
  let pols, rule_order = type_trules_compilation tprog compilation_rules in
  let pols = Map.map pols ~f:fst in (* remove transparency information from pols *)
  let erules = erules_from_compilation_rules compilation_rules in
  let e_compilation_rules = convert_compilation_rules tprog pols b compilation_rules in
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
