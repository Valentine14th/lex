(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base

open Formula
open Tformula
open Tlex
open Elex

let rec is_past_guarded s x p f =
  let r =
  match f with
  | TTT | TFF -> false
  | TEqConst (x', y) ->
     begin
       match Tlex.unpack_special_eq s.tevents x' y with
       | Some (event_name, trms) -> is_past_guarded s x p (TPredicate (event_name, trms))
       | None -> p && Term.equal_core (Term.TVar x) x'.trm && Term.is_const y.trm
     end
  | TPredicate (_, ts) -> List.exists ~f:(fun t -> Term.equal_core (Term.TVar x) t.trm) ts
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
    | ECast of string * EnfType.t * EnfType.t
    | EFormula of string option * t * EnfType.t
    | EConj of error * error
    | EDisj of error * error

  let rec to_string ?(n=0) e =
    let sp = Util.spaces (2*n) in
    let lb = "\n" ^ sp in
    (match e with
     | ECast (e, t', t) -> Printf.sprintf "make %s %s (currently, it has type %s)"
                             e (EnfType.to_string t) (EnfType.to_string t')
     | EFormula (None, f, t) -> Printf.sprintf "make %s %s, but this is impossible"
                                  (Tformula.to_string f) (EnfType.to_string t)
     | EFormula (Some s, f, t) -> Printf.sprintf "make %s %s, but this is impossible (%s)"
                                    (Tformula.to_string f) (EnfType.to_string t) s
     | EConj (f, g) -> Printf.sprintf "both%s* %s%sand%s* %s"
                         lb (to_string ~n:(n+1) f) lb lb (to_string ~n:(n+1) g)
     | EDisj (f, g) -> Printf.sprintf "either%s* %s%sor%s* %s"
                         lb (to_string ~n:(n+1) f) lb lb (to_string ~n:(n+1) g)
    )

end

module Constraints = struct

  type constr =
    | CTT
    | CFF
    | CEq of string * EnfType.t
    | CConj of constr * constr
    | CDisj of constr * constr [@@deriving compare, sexp_of]

  let rec equal c c' = match c, c' with
    | CTT, CTT -> true
    | CFF, CFF -> true
    | CEq (s, ty), CEq (s', ty') -> String.equal s s' && EnfType.equal ty ty'
    | CConj (c1, c2), CConj (c1', c2') -> equal c1 c1' && equal c2 c2'
    | CDisj (c1, c2), CDisj (c1', c2') -> equal c1 c1' && equal c2 c2'
    | _, _ -> false

  type verdict = Possible of constr | Impossible of Errors.error

  let tt = CTT
  let ff = CFF
  let eq s t = CEq (s, t)

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
    | `Left t | `Right t -> Some t
    | `Both (t, u) -> if EnfType.equal t u then Some t else raise CannotMerge

  let try_merge (a, b) =
    try Some (Map.merge a b ~f:merge_aux)
    with CannotMerge -> None

  let rec solve = function
    | CTT -> [Map.empty (module String)]
    | CFF -> []
    | CEq (s, t) -> [Map.singleton (module String) s t]
    | CConj (c, d) -> List.filter_map (cartesian (solve c) (solve d)) ~f:try_merge
    | CDisj (c, d) -> (solve c) @ (solve d)

  let rec to_string_rec l = function
    | CTT -> Printf.sprintf "⊤"
    | CFF -> Printf.sprintf "⊥"
    | CEq (s, t) -> Printf.sprintf "t(%s) = %s" s (EnfType.to_string t)
    | CConj (c, d) -> Printf.sprintf (Util.paren l 4 "%a ∧ %a") (fun _ -> to_string_rec 4) c (fun _ -> to_string_rec 4) d
    | CDisj (c, d) -> Printf.sprintf (Util.paren l 3 "%a ∨ %a") (fun _ -> to_string_rec 3) c (fun _ -> to_string_rec 4) d

  let to_string = to_string_rec 0

end

open EnfType
open Constraints
open Option

(* todo: ensure that there is no shadowing *)

let types_predicate pols t e =
  let t' = Map.find_exn pols e in
  match t', t with
  | _, _ when EnfType.equal t t' -> Possible CTT
  | CauSup, _ -> Possible (eq e t)
  | _, _      -> Impossible (ECast (e, t', t))

let rec types s pols t f =
  let error s = Impossible (EFormula (Some s, f, t)) in
  match t with
  | Cau -> begin
      match f with
      | TTT -> Possible CTT
      | TEqConst (x', y) ->
         begin
           match Tlex.unpack_special_eq s.tevents x' y with
           | Some (e, trms) -> types s pols Cau (TPredicate (e, trms))
           | None -> Impossible (EFormula (None, f, t))
         end
      | TPredicate (e, _) -> types_predicate pols Cau e
      | TNeg f -> types s pols Sup f
      | TAnd (_, fs) ->
         List.fold_left (List.map fs ~f:(types s pols Cau)) ~init:(Possible CTT) ~f:conj
      | TOr (L, fs) -> types s pols Cau (List.hd_exn fs)
      | TOr (R, fs) -> types s pols Cau (List.last_exn fs)
      | TOr (_, fs) ->
         List.fold_left (List.map fs ~f:(types s pols Cau)) ~init:(Possible CTT) ~f:disj
      | TImp (L, f, _) -> types s pols Sup f
      | TImp (R, _, g) -> types s pols Cau g
      | TImp (_, f, g) -> disj (types s pols Sup f) (types s pols Cau g)
      | TIff (L, L, f, _) -> conj (types s pols Sup f) (types s pols Cau f)
      | TIff (L, R, f, g) -> conj (types s pols Sup f) (types s pols Sup g)
      | TIff (R, L, f, g) -> conj (types s pols Cau g) (types s pols Cau f)
      | TIff (R, R, _, g) -> conj (types s pols Cau g) (types s pols Sup g)
      | TIff (_, _, f, g) -> conj (disj (types s pols Sup f) (types s pols Cau g))
                              (disj (types s pols Cau f) (types s pols Sup g))
      | TExists (_, f) -> types s pols Cau f
      | TForall (x, f) when is_past_guarded s x false f -> types s pols Cau f
      | TForall (x, _) -> error ("for causability " ^ x ^ " must be past-guarded")
      | TNext (i, f) when Interval.equal i Interval.full -> types s pols Cau f
      | TNext _ -> error "○ with non-[0,∞) interval is never Cau"
      | TOnce (i, g) | TSince (_, i, _, g) when Interval.has_zero i -> types s pols Cau g
      | TOnce _ | TSince _ -> error "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      | TEventually (_, f) | TAlways (_, f) -> types s pols Cau f
      | TUntil (LR, B _, f, g) -> conj (types s pols Cau f) (types s pols Cau g)
      | TUntil (_, i, _, g) when Interval.has_zero i -> types s pols Cau g
      | TUntil (_, _, f, g) -> conj (types s pols Cau f) (types s pols Cau g)
      | TPrev _ -> error "● is never Cau"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Sup -> begin
      match f with
      | TFF -> Possible CTT
      | TEqConst (x', y) ->
         begin
           match Tlex.unpack_special_eq s.tevents x' y with
           | Some (e, trms) -> types s pols Sup (TPredicate (e, trms))
           | None -> Impossible (EFormula (None, f, t))
         end
      | TPredicate (e, _) -> types_predicate pols Sup e
      | TNeg f -> types s pols Cau f
      | TAnd (L, fs) -> types s pols Sup (List.hd_exn fs)
      | TAnd (R, fs) -> types s pols Sup (List.last_exn fs)
      | TAnd (_, fs) ->
         List.fold_left (List.map fs ~f:(types s pols Cau)) ~init:(Possible CTT) ~f:disj
      | TOr (_, fs) ->
         List.fold_left (List.map fs ~f:(types s pols Cau)) ~init:(Possible CTT) ~f:conj
      | TImp (_, f, g) -> conj (types s pols Cau f) (types s pols Sup g)
      | TIff (L, _, f, g) -> conj (types s pols Cau f) (types s pols Sup g)
      | TIff (R, _, f, g) -> conj (types s pols Sup f) (types s pols Cau g)
      | TIff (_, _, f, g) -> disj (conj (types s pols Cau f) (types s pols Sup g))
                              (conj (types s pols Sup f) (types s pols Cau g))
      | TExists (x, f) when is_past_guarded s x true f -> types s pols Sup f
      | TExists (x, _) -> error ("for suppressability " ^ x ^ " must be past-guarded")
      | TForall (_, f) -> types s pols Sup f
      | TNext (_, f) -> types s pols Sup f
      | THistorically (i, f) when Interval.has_zero i -> types s pols Sup f
      | THistorically _ -> error "■[a,b) with a > 0 is never Sup"
      | TSince (_, i, f, _) when not (Interval.has_zero i) -> types s pols Sup f
      | TSince (_, _, f, g) -> conj (types s pols Sup f) (types s pols Sup g)
      | TEventually (_, f) | TAlways (_, f) -> types s pols Sup f
      | TUntil (L, i, f, _) when not (Interval.has_zero i) -> types s pols Sup f
      | TUntil (R, i, _, g) when not (Interval.has_zero i) -> types s pols Sup g
      | TUntil (_, i, f, g) when not (Interval.has_zero i) -> disj (types s pols Sup f) (types s pols Sup g)
      | TUntil (_, _, _, g) -> types s pols Sup g
      | TPrev _ -> error "● is never Sup"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Obs -> Possible CTT
  | _ -> Impossible (EFormula (None, f, t))

(* todo [FH]: Extend to set ids *)
let rec convert s (pols: ('a, 'b, 'c) Base.Map.t) b enftype form : Eformula.t option =
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
        | TEqConst (x', y) ->
         begin
           match Tlex.unpack_special_eq s.tevents x' y with
           | Some (e, t) when EnfType.equal (Map.find_exn pols e) Cau -> Some (Eformula.EPredicate (e, t))
           | _ -> None
         end
        | TPredicate (e, t) when EnfType.equal (Map.find_exn pols e) Cau -> Some (Eformula.EPredicate (e, t))
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
        | TEqConst (x', y) ->
         begin
           match Tlex.unpack_special_eq s.tevents x' y with
           | Some (e, t) when EnfType.equal (Map.find_exn pols e) Sup -> Some (Eformula.EPredicate (e, t))
           | _ -> None
         end
        | TPredicate (e, t) when EnfType.equal (Map.find_exn pols e) Sup -> Some (Eformula.EPredicate (e, t))
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

let convert_enforceable s pols f b pos =
  if not (Set.is_empty (Tformula.fv f)) then
    ignore (raise (Invalid_argument (Printf.sprintf "formula %s is not closed" (Tformula.to_string f))));
  match types pols s Cau f with
  | Possible c ->
     begin
       match Constraints.solve c with
       | sol::_ ->
          begin
            (*Map.iteri sol ~f:(fun ~key ~data -> Pred.Sig.update_enftype key data);*)
            ignore sol; (* todo [FH]: check consistency of solutions over formulae *)
            match convert pols s b Cau f with
              Some f' -> f'
            | None    -> let err_msg = Printf.sprintf "formula\n %s\ncannot be converted" (Tformula.to_string f) in
                         Util.type_error err_msg pos
          end
       | _ -> let err_msg = Printf.sprintf "formula\n %s\n is not enforceable becuase the constraint\n %s\nhas no solution"
                              (Tformula.to_string f) (Constraints.to_string c) in
              Util.type_error err_msg pos
     end
  | Impossible e ->
     let err_msg = Printf.sprintf "The formula\n %s\nis not enforceable. To make it enforceable, you would need to\n %s"
                     (Tformula.to_string f) (Errors.to_string e) in
     Util.type_error err_msg pos

let rec relative_interval (f: Eformula.t) =
  match f.f with
  | ETT | EFF | EEqConst (_, _) | EPredicate (_, _) -> Zinterval.singleton 0
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

let strict f =
  let rec _strict itv fut (f: Eformula.t) =
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

let relative_past f =
  Zinterval.is_nonpositive (relative_interval f)

let strictly_relative_past f =
  (relative_past f) && (strict f)

let is_transparent (f: Eformula.t) =
  let rec aux (f: Eformula.t) =
    match f.enftype with
    | Cau -> begin
        match f.f with
        | ETT | EPredicate (_, _) -> true
        | ENeg f | EExists (_, f) | EForall (_, f)
          | EOnce (_, f) | ENext (_, f) | EHistorically (_, f)
           | EAlways (_, _, f) -> aux f
        | EEventually (_, b, f) -> b && aux f
        | EImp (L, f, g) | EIff (L, L, f, g)
          -> aux f && strictly_relative_past g
        | EOr (L, f :: fs)
          -> aux f && List.for_all fs ~f:strictly_relative_past
        | EImp (R, f, g) | EIff (R, R, f, g)
           -> aux g && strictly_relative_past f
        | EOr (R, fs)
          -> aux (List.last_exn fs) && List.for_all (List.drop_last_exn fs) ~f:strictly_relative_past
        | EAnd (_, fs) -> List.for_all fs ~f:aux
        | EIff (_, _, f, g) -> aux f && aux g
        | ESince (_, _, f, g) -> aux f && strictly_relative_past g
        | EUntil (R, _, b, f, g) -> b && aux f && strictly_relative_past g
        | EUntil (LR, _, b, f, g) -> b && aux f && aux g
        | _ -> false
      end
    | Sup -> begin
        match f.f with
        | EFF | EPredicate (_, _) -> true
        | ENeg f | EExists (_, f) | EForall (_, f)
          | EOnce (_, f) | ENext (_, f) | EHistorically (_, f)
          | EEventually (_, _, f) -> aux f
        | EAlways (_, b, f) -> b && aux f
        | EAnd (L, f :: fs) -> aux f  && List.for_all fs ~f:strictly_relative_past
        | EIff (L, L, f, g) -> aux f && strictly_relative_past g
        | EIff (R, R, f, g)
          -> aux g && strictly_relative_past f
        | EAnd (R, fs) -> aux (List.last_exn fs) && List.for_all (List.drop_last_exn fs) ~f:strictly_relative_past
        | EIff (_, _, f, g) -> aux f && aux g
        | EOr (_, fs) -> List.for_all fs ~f:aux
        | ESince (L, _, f, g) -> aux f && strictly_relative_past g
        | ESince (R, _, f, g) -> aux f && aux g
        | EUntil (R, _, _, f, g) -> aux f && strictly_relative_past g
        | EUntil (_, _, _, f, g) -> aux g && strictly_relative_past f
        | _ -> false
      end
    | _ -> assert false
  in
  aux f

let convert_transparently_enforceable s pols f b pos =
  let f' = convert_enforceable s pols f b pos in
  if is_transparent f' then
    f'
  else
    let err_msg = Printf.sprintf "The formula\n %s\nis not transparently enforceable."
                     (Tformula.to_string f) in
    Util.type_error err_msg pos

let epattern_of_tpattern s = function
  | TPPresent -> EPPresent
  | TPEventually i -> EPEventually i
  | TPAlways i -> EPAlways i
  | TPUntil (i, f) -> EPUntil (i, Eformula.of_tformula s.tevents f)
  | TPOnce i -> EPOnce i
  | TPHistorically i -> EPHistorically i
  | TPSince (i, f) -> EPSince (i, Eformula.of_tformula s.tevents f)

(* TODO: type check formulas with information in pols *)
(* let type_trule pols = function *)
let type_trule s _ =
  let of_tformulas f =
    List.map f ~f:(fun (p,f') -> (p, Eformula.of_tformula s.tevents f')) in
  function
  | TSRule (pos, idx, label, type_fixes, rule, rule_type, rule_constrs, doc_string) -> begin
      let rule =  (*[FH] todo, filler code!*) 
        match rule with
        | TException (f1, p, refs, f2) -> 
           EException (of_tformulas f1, epattern_of_tpattern s p, refs, Eformula.of_tformula s.tevents f2)
        | TScope (f1, p, refs, f2) -> 
           EScope (of_tformulas f1, epattern_of_tpattern s p, refs, Eformula.of_tformula s.tevents f2)
        | TObligation (f1, p, f2, q) ->
           EObligation (of_tformulas f1, epattern_of_tpattern s p, of_tformulas f2, epattern_of_tpattern s q)
        | TPermission (f1, p, f2, q) ->
           EPermission (of_tformulas f1, epattern_of_tpattern s p, of_tformulas f2, epattern_of_tpattern s q)
        | TConstitutive (f1, p, f2) ->
           EConstitutive (of_tformulas f1, epattern_of_tpattern s p, List.map f2 ~f:(fun (p,f') -> (p, Eformula.of_tformula s.tevents f')))
      in
      ESRule (pos, idx, label, type_fixes, rule, rule_type, rule_constrs, doc_string)
    end
  | _ -> assert false

let type_tstmt s pols = function
  | TSImport (pos, idents, import_format) ->
     ESImport (pos, idents, import_format)
  | TSSection (section_kind, full_label, label, title) -> 
     ESSection (section_kind, full_label, label, title)
  | TSRule _ as trule -> type_trule s pols trule
  | TSEvent (event_type, name, typed_args, pol, doc_string) ->
     ESEvent (event_type, name, typed_args, pol, doc_string)
  | TSType (name, typ, doc_string) -> ESType (name, typ, doc_string)
  | TSFunction (name, arg_types, return_type, doc_string) ->
     ESFunction (name, arg_types, return_type, doc_string)
  | TSNote text -> ESNote text

let type_exception s _ f = Eformula.of_tformula s.tevents f

let type_scope s _ f = Eformula.of_tformula s.tevents f

(* let type_exceptions pol exceptions =
  List.map exceptions ~f:(type_exception pol)

let type_scopes pol scopes =
  List.map scopes ~f:(type_scope pol) *)

let do_type _ tprog =
  let pols = Tlex.pol_map tprog in
  {
    estmts     = List.map tprog.tstmts ~f:(type_tstmt tprog pols);
    ealiases   = tprog.taliases;
    eevents    = tprog.tevents;
    efunctions = tprog.tfunctions;
    variables  = tprog.variables;
    rule_tree  = tprog.rule_tree;
    exception_predicates = Map.map tprog.exception_predicates ~f:(type_exception tprog pols);
    scope_predicates     = Map.map tprog.scope_predicates ~f:(type_scope tprog pols);
  }
