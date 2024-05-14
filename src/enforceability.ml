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

open Tlex
open Elex

let rec is_past_guarded x p f =
  let r =
  match f with
  | TT | FF -> false
  | EqConst (y, _) -> p && String.equal x y
  | Predicate (_, ts) -> List.exists ~f:(Term.equal (Term.Var x)) ts
  | Neg f -> is_past_guarded x (not p) f
  | And (_, fs) when p -> List.exists fs ~f:(is_past_guarded x p)
  | And (_, fs) -> List.for_all fs ~f:(is_past_guarded x p)
  | Or (_, fs) when p -> List.for_all fs ~f:(is_past_guarded x p)
  | Or (_, fs) -> List.exists fs ~f:(is_past_guarded x p)
  | Imp (_, f, g) when p -> is_past_guarded x (not p) f && is_past_guarded x p g
  | Imp (_, f, g) -> is_past_guarded x (not p) f || is_past_guarded x p g
  | Iff (_, _, f, g) when p -> is_past_guarded x (not p) f && is_past_guarded x p g
                               || is_past_guarded x p f && is_past_guarded x (not p) g
  | Iff (_, _, f, g) -> (is_past_guarded x (not p) f || is_past_guarded x p g)
                        && (is_past_guarded x p f || is_past_guarded x (not p) g)
  | Exists (y, f) | Forall (y, f) -> not (String.equal x y) && is_past_guarded x p f
  | Prev (_, f) -> p && is_past_guarded x p f
  | Once (_, f) | Eventually (_, f) when p -> is_past_guarded x p f
  | Once (i, f) | Eventually (i, f) -> Interval.mem 0 i && is_past_guarded x p f
  | Historically (_, f) | Always (_, f) when not p -> is_past_guarded x p f
  | Historically (i, f) -> Interval.mem 0 i && is_past_guarded x p f
  | Since (_, i, f, g) when p -> not (Interval.mem 0 i) && is_past_guarded x p f
                                 || is_past_guarded x p g
  | Until (_, i, f, g) when p -> not (Interval.mem 0 i) && is_past_guarded x p f
                                 || is_past_guarded x p f && is_past_guarded x p g
  | Since (_, i, _, g) | Until (_, i, _, g) -> Interval.mem 0 i && is_past_guarded x p g
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
                                  (Formula.to_string f) (EnfType.to_string t)
     | EFormula (Some s, f, t) -> Printf.sprintf "make %s %s, but this is impossible (%s)"
                                    (Formula.to_string f) (EnfType.to_string t) s
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

let rec types pols t f =
  let error s = Impossible (EFormula (Some s, f, t)) in
  match t with
  | Cau -> begin
      match f with
      | TT -> Possible CTT
      | Predicate (e, _) -> types_predicate pols Cau e
      | Neg f -> types pols Sup f
      | And (_, fs) ->
         List.fold_left (List.map fs ~f:(types pols Cau)) ~init:(Possible CTT) ~f:conj
      | Or (L, fs) -> types pols Cau (List.hd_exn fs)
      | Or (R, fs) -> types pols Cau (List.last_exn fs)
      | Or (_, fs) ->
         List.fold_left (List.map fs ~f:(types pols Cau)) ~init:(Possible CTT) ~f:disj
      | Imp (L, f, _) -> types pols Sup f
      | Imp (R, _, g) -> types pols Cau g
      | Imp (_, f, g) -> disj (types pols Sup f) (types pols Cau g)
      | Iff (L, L, f, _) -> conj (types pols Sup f) (types pols Cau f)
      | Iff (L, R, f, g) -> conj (types pols Sup f) (types pols Sup g)
      | Iff (R, L, f, g) -> conj (types pols Cau g) (types pols Cau f)
      | Iff (R, R, _, g) -> conj (types pols Cau g) (types pols Sup g)
      | Iff (_, _, f, g) -> conj (disj (types pols Sup f) (types pols Cau g))
                              (disj (types pols Cau f) (types pols Sup g))
      | Exists (_, f) -> types pols Cau f
      | Forall (x, f) when is_past_guarded x false f -> types pols Cau f
      | Forall (x, _) -> error ("for causability " ^ x ^ " must be past-guarded")
      | Next (i, f) when Interval.equal i Interval.full -> types pols Cau f
      | Next _ -> error "○ with non-[0,∞) interval is never Cau"
      | Once (i, g) | Since (_, i, _, g) when Interval.mem 0 i -> types pols Cau g
      | Once _ | Since _ -> error "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      | Eventually (_, f) | Always (_, f) -> types pols Cau f
      | Until (LR, B _, f, g) -> conj (types pols Cau f) (types pols Cau g)
      | Until (_, i, _, g) when Interval.mem 0 i -> types pols Cau g
      | Until (_, _, f, g) -> conj (types pols Cau f) (types pols Cau g)
      | Prev _ -> error "● is never Cau"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Sup -> begin
      match f with
      | FF -> Possible CTT
      | Predicate (e, _) -> types_predicate pols Sup e
      | Neg f -> types pols Cau f
      | And (L, fs) -> types pols Sup (List.hd_exn fs)
      | And (R, fs) -> types pols Sup (List.last_exn fs)
      | And (_, fs) ->
         List.fold_left (List.map fs ~f:(types pols Cau)) ~init:(Possible CTT) ~f:disj
      | Or (_, fs) ->
         List.fold_left (List.map fs ~f:(types pols Cau)) ~init:(Possible CTT) ~f:conj
      | Imp (_, f, g) -> conj (types pols Cau f) (types pols Sup g)
      | Iff (L, _, f, g) -> conj (types pols Cau f) (types pols Sup g)
      | Iff (R, _, f, g) -> conj (types pols Sup f) (types pols Cau g)
      | Iff (_, _, f, g) -> disj (conj (types pols Cau f) (types pols Sup g))
                              (conj (types pols Sup f) (types pols Cau g))
      | Exists (x, f) when is_past_guarded x true f -> types pols Sup f
      | Exists (x, _) -> error ("for suppressability " ^ x ^ " must be past-guarded")
      | Forall (_, f) -> types pols Sup f
      | Next (_, f) -> types pols Sup f
      | Historically (i, f) when Interval.mem 0 i -> types pols Sup f
      | Historically _ -> error "■[a,b) with a > 0 is never Sup"
      | Since (_, i, f, _) when not (Interval.mem 0 i) -> types pols Sup f
      | Since (_, _, f, g) -> conj (types pols Sup f) (types pols Sup g)
      | Eventually (_, f) | Always (_, f) -> types pols Sup f
      | Until (L, i, f, _) when not (Interval.mem 0 i) -> types pols Sup f
      | Until (R, i, _, g) when not (Interval.mem 0 i) -> types pols Sup g
      | Until (_, i, f, g) when not (Interval.mem 0 i) -> disj (types pols Sup f) (types pols Sup g)
      | Until (_, _, _, g) -> types pols Sup g
      | Prev _ -> error "● is never Sup"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Obs -> Possible CTT
  | _ -> Impossible (EFormula (None, f, t))

(* todo [FH]: Extend to set ids *)
let rec convert (pols: ('a, 'b, 'c) Base.Map.t) b enftype form : Tformula.t option =
  let convert = convert pols b in
  let default_L (s: Side.t) = if Side.equal s R then Side.R else L in
  let set_b = function
    | Interval.U (UI a) -> Interval.B (BI (a, b))
    | B _ as i -> i in
  let f =
    match enftype with
      Cau -> begin
        match form with
        | TT -> Some (Tformula.TTT)
        | Predicate (e, t) when EnfType.equal (Map.find_exn pols e) Cau -> Some (Tformula.TPredicate (e, t))
        | Neg f -> (convert Sup f) >>| (fun f' -> Tformula.TNeg f')
        | And (s, fs) ->
           Option.all (List.map fs ~f:(convert Cau))
           >>| (fun fs' -> Tformula.TAnd (default_L s, fs'))
        | Or (L, f :: fs) ->
           (convert Cau f)
           >>| (fun f' -> Tformula.TOr(L, f' :: (Tformula.of_formulas fs)))
        | Or (R, fs) ->
           let f, fs = List.last_exn fs, List.drop_last_exn fs in
           (convert Cau f) >>| (fun f' -> Tformula.TOr(R, (Tformula.of_formulas fs) @ [f']))
        | Or (_, fs) ->
           begin
             match convert Cau (List.hd_exn fs) with
             | Some f' -> Some (Tformula.TOr (L, f' :: (Tformula.of_formulas fs)))
             | None    ->
                let f, fs = List.last_exn fs, List.drop_last_exn fs in
                (convert Cau f) >>| (fun f' -> Tformula.TOr (R, (Tformula.of_formulas fs) @ [f']))
           end
        | Imp (L, f, g) -> (convert Sup f) >>| (fun f' -> Tformula.TImp(L, f', Tformula.of_formula g))
        | Imp (R, f, g) -> (convert Cau g) >>| (fun g' -> Tformula.TImp(R, Tformula.of_formula f, g'))
        | Imp (_, f, g) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Tformula.TImp (L, f', Tformula.of_formula g))
             | None    -> (convert Cau g) >>| (fun g' -> Tformula.TImp (R, Tformula.of_formula f, g'))
           end
        | Iff (L, L, f, g) -> (convert Sup f) >>| (fun f' -> Tformula.TIff (L, L, f', Tformula.of_formula g))
        | Iff (L, R, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                             >>| (fun g' -> Tformula.TIff (L, R, f', g')))
        | Iff (R, L, f, g) -> (convert Cau g) >>= (fun g' -> (convert Cau f)
                                                             >>| (fun f' -> Tformula.TIff (R, L, f', g')))
        | Iff (R, R, f, g) -> (convert Cau g) >>| (fun g' -> Tformula.TIff (R, R, Tformula.of_formula f, g'))
        | Iff (_, _, f, g) ->
           begin
             match convert Sup f with
             | Some f' ->
                begin
                  match convert Cau f with
                  | Some f' -> Some (Tformula.TIff (L, L, f', Tformula.of_formula g))
                  | None    -> (convert Sup g) >>| (fun g' -> Tformula.TIff (L, R, f', g'))
                end
             | None -> (convert Cau g)
                       >>= (fun g' ->
                 match convert Cau f with
                 | Some f' -> Some (Tformula.TIff (R, L, f', g'))
                 | None    -> (convert Sup g) >>| (fun g' -> Tformula.TIff (R, R, Tformula.of_formula f, g')))
           end
        | Exists (x, f) -> (convert Cau f) >>| (fun f' -> Tformula.TExists (x, f'))
        | Forall (x, f) when is_past_guarded x false f -> (convert Cau f) >>| (fun f' -> Tformula.TForall (x, f'))
        | Next (i, f) when Interval.equal i Interval.full ->
           (convert Cau f) >>| (fun f' -> Tformula.TNext (i, f'))
        | Once (i, f) when Interval.mem 0 i ->
           (convert Cau f) >>| (fun f' -> Tformula.TOnce (i, f'))
        | Since (_, i, f, g) when Interval.mem 0 i ->
           (convert Cau g) >>| (fun g' -> Tformula.TSince (R, i, Tformula.of_formula f, g'))
        | Eventually (i, f) -> (convert Cau f) >>| (fun f' -> Tformula.TEventually (set_b i, Interval.is_bounded i, f'))
        | Always (i, f) -> (convert Cau f) >>| (fun f' -> Tformula.TAlways (i, true, f'))
        | Until (LR, i, f, g) ->
           (convert Cau f) >>= (fun f' -> (convert Cau g) >>| (fun g' -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, f', g')))
        | Until (_, i, f, g) when Interval.mem 0 i ->
           (convert Cau g) >>| (fun g' -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, Tformula.of_formula f, g'))
        | Until (L, i, f, g) ->
           (convert Cau g) >>| (fun g' -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, Tformula.of_formula f, g'))
        | _ -> None
      end
    | Sup -> begin
        match form with
        | FF -> Some (Tformula.TFF)
        | Predicate (e, t) when EnfType.equal (Map.find_exn pols e) Sup -> Some (Tformula.TPredicate (e, t))
        | Neg f -> (convert Cau f) >>| (fun f' -> Tformula.TNeg f')
        | And (L, f :: fs) -> (convert Sup f) >>| (fun f' -> Tformula.TAnd (L, f' :: (Tformula.of_formulas fs)))
        | And (R, fs) ->
           let f, fs = List.last_exn fs, List.drop_last_exn fs in
           (convert Sup f) >>| (fun f' -> Tformula.TAnd (R, (Tformula.of_formulas fs) @ [f']))
        | And (_, fs) ->
           begin
              match convert Sup (List.hd_exn fs) with
             | Some f' -> Some (Tformula.TAnd (L, f' :: (Tformula.of_formulas (List.tl_exn fs))))
             | None    ->
                let f, fs = List.last_exn fs, List.drop_last_exn fs in
                (convert Sup f) >>| (fun f' -> Tformula.TAnd (R, (Tformula.of_formulas fs) @ [f']))
           end
        | Or (s, fs) ->
           Option.all (List.map fs ~f:(convert Sup))
           >>| (fun fs' -> Tformula.TOr (default_L s, fs'))
        | Imp (s, f, g) -> (convert Cau f) >>= (fun f' -> (convert Sup g)
                                                          >>| (fun g' -> Tformula.TImp (default_L s, f', g')))
        | Iff (L, _, f, g) -> (convert Cau f) >>= (fun f' -> (convert Sup g)
                                                             >>| (fun g' -> Tformula.TIff (L, N, f', g')))
        | Iff (R, _, f, g) -> (convert Sup f) >>= (fun f' -> (convert Cau g)
                                                             >>| (fun g' -> Tformula.TIff (R, N, f', g')))
        | Iff (_, _, f, g) ->
           begin
             match convert Cau f, convert Sup g with
             | Some f', Some g' -> Some (Tformula.TIff (L, R, f', g'))
             | _, _ -> match convert Sup f, convert Cau g with
                       | Some f', Some g' -> Some (Tformula.TIff(R, L, f', g'))
                       | _, _ -> None
           end
        | Exists (x, f) when is_past_guarded x true f ->
           (convert Sup f) >>| (fun f' -> Tformula.TExists (x, f'))
        | Forall (x, f) ->  (convert Sup f) >>| (fun f' -> Tformula.TForall (x, f'))
        | Next (i, f) -> (convert Sup f) >>= (fun f' -> Some (Tformula.TNext (i, f')))
        | Historically (i, f) when Interval.mem 0 i ->
           (convert Sup f) >>| (fun f' -> Tformula.THistorically (i, f'))
        | Since (_, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup f) >>| (fun f' -> Tformula.TSince (L, i, f', Tformula.of_formula g))
        | Since (_, i, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                                    >>| (fun g' -> Tformula.TSince (LR, i, f', g')))
        | Eventually (i, f) -> (convert Sup f) >>| (fun f' -> Tformula.TEventually (i, true, f'))
        | Always (i, f) -> (convert Sup f) >>| (fun f' -> Tformula.TAlways (set_b i, Interval.is_bounded i, f'))
        | Until (L, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup f) >>| (fun f' -> Tformula.TUntil (L, i, true, f', Tformula.of_formula g))
        | Until (R, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup g) >>| (fun g' -> Tformula.TUntil (R, i, true, Tformula.of_formula f, g'))
        | Until (_, i, f, g) when not (Interval.mem 0 i) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Tformula.TUntil (L, i, true, f', Tformula.of_formula g))
             | None -> (convert Sup g) >>| (fun g' -> Tformula.TUntil (R, i, true, Tformula.of_formula f, g'))
           end
        | Until (_, i, f, g) -> (convert Sup g) >>| (fun g' -> Tformula.TUntil (R, i, true, Tformula.of_formula f, g'))
        | _ -> None
      end
    | Obs -> Some (Tformula.of_formula form).f
    | _ -> assert false
  in
  (*Stdio.print_string (EnfType.to_string enftype ^ " " ^ Formula.to_string form ^ " -> ");*)
  match f with Some f -> Some Tformula.{ f; enftype; id = 0 } | None -> None

let convert_enforceable pols f b pos =
  if not (Set.is_empty (Formula.fv f)) then
    ignore (raise (Invalid_argument (Printf.sprintf "formula %s is not closed" (Formula.to_string f))));
  match types pols Cau f with
  | Possible c ->
     begin
       match Constraints.solve c with
       | sol::_ ->
          begin
            (*Map.iteri sol ~f:(fun ~key ~data -> Pred.Sig.update_enftype key data);*)
            ignore sol; (* todo [FH]: check consistency of solutions over formulae *)
            match convert pols b Cau f with
              Some f' -> f'
            | None    -> let err_msg = Printf.sprintf "formula\n %s\ncannot be converted" (Formula.to_string f) in
                         Util.type_error err_msg pos
          end
       | _ -> let err_msg = Printf.sprintf "formula\n %s\n is not enforceable becuase the constraint\n %s\nhas no solution"
                              (Formula.to_string f) (Constraints.to_string c) in
              Util.type_error err_msg pos
     end
  | Impossible e ->
     let err_msg = Printf.sprintf "The formula\n %s\nis not enforceable. To make it enforceable, you would need to\n %s"
                     (Formula.to_string f) (Errors.to_string e) in
     Util.type_error err_msg pos

let rec relative_interval (f: Tformula.t) =
  match f.f with
  | TTT | TFF | TEqConst (_, _) | TPredicate (_, _) -> Zinterval.singleton 0
  | TNeg f | TExists (_, f) | TForall (_, f) -> relative_interval f
  | TAnd (_, fs) | TOr (_, fs)
    -> List.fold_left (List.map fs ~f:relative_interval) ~init:Zinterval.full ~f:Zinterval.lub
  | TImp (_, f1, f2) | TIff (_, _, f1, f2)
    -> Zinterval.lub (relative_interval f1) (relative_interval f2)
  | TPrev (i, f) | TOnce (i, f) | THistorically (i, f)
    -> let i' = Zinterval.inv (Zinterval.of_interval i) in
       Zinterval.lub (Zinterval.to_zero i') (Zinterval.sum i' (relative_interval f))
  | TNext (i, f) | TEventually (i, _, f) | TAlways (i, _, f)
    -> let i = Zinterval.of_interval i in
       Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i (relative_interval f))
  | TSince (_, i, f1, f2) ->
     let i' = Zinterval.inv (Zinterval.of_interval i) in
     (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
        (Zinterval.sum i' (relative_interval f2)))
  | TUntil (_, i, _, f1, f2) ->
     let i' = Zinterval.of_interval i in
     (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
        (Zinterval.sum i' (relative_interval f2)))
  | TType (f, _) -> relative_interval f

let strict f =
  let rec _strict itv fut (f: Tformula.t) =
    ((Zinterval.mem 0 itv) && fut)
    || (match f.f with
        | TTT | TFF | TEqConst (_, _) | TPredicate _ -> false
        | TNeg f | TExists (_, f) | TForall (_, f) -> _strict itv fut f
        | TImp (_, f1, f2) | TIff (_, _, f1, f2)
          -> (_strict itv fut f1) || (_strict itv fut f2)
        | TAnd (_, fs) | TOr (_, fs)
          -> List.exists fs ~f:(_strict itv fut)
        | TPrev (i, f) | TOnce (i, f) | THistorically (i, f)
          -> _strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f
        | TNext (i, f) | TEventually (i, _, f) | TAlways (i, _, f)
          -> _strict (Zinterval.sum (Zinterval.of_interval i) itv) true f
        | TSince (_, i, f1, f2)
          -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f1)
             || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f2)
        | TUntil (_, i, _, f1, f2)
          -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f1)
             || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f2)
        | TType (f, _) -> _strict itv fut f)
  in not (_strict (Zinterval.singleton 0) false f)

let relative_past f =
  Zinterval.is_nonpositive (relative_interval f)

let strictly_relative_past f =
  (relative_past f) && (strict f)

let is_transparent (f: Tformula.t) =
  let rec aux (f: Tformula.t) =
    match f.enftype with
    | Cau -> begin
        match f.f with
        | TTT | TPredicate (_, _) -> true
        | TNeg f | TExists (_, f) | TForall (_, f)
          | TOnce (_, f) | TNext (_, f) | THistorically (_, f)
           | TAlways (_, _, f) -> aux f
        | TEventually (_, b, f) -> b && aux f
        | TImp (L, f, g) | TIff (L, L, f, g)
          -> aux f && strictly_relative_past g
        | TOr (L, f :: fs)
          -> aux f && List.for_all fs ~f:strictly_relative_past
        | TImp (R, f, g) | TIff (R, R, f, g)
           -> aux g && strictly_relative_past f
        | TOr (R, fs)
          -> aux (List.last_exn fs) && List.for_all (List.drop_last_exn fs) ~f:strictly_relative_past
        | TAnd (_, fs) -> List.for_all fs ~f:aux
        | TIff (_, _, f, g) -> aux f && aux g
        | TSince (_, _, f, g) -> aux f && strictly_relative_past g
        | TUntil (R, _, b, f, g) -> b && aux f && strictly_relative_past g
        | TUntil (LR, _, b, f, g) -> b && aux f && aux g
        | _ -> false
      end
    | Sup -> begin
        match f.f with
        | TFF | TPredicate (_, _) -> true
        | TNeg f | TExists (_, f) | TForall (_, f)
          | TOnce (_, f) | TNext (_, f) | THistorically (_, f)
          | TEventually (_, _, f) -> aux f
        | TAlways (_, b, f) -> b && aux f
        | TAnd (L, f :: fs) -> aux f  && List.for_all fs ~f:strictly_relative_past
        | TIff (L, L, f, g) -> aux f && strictly_relative_past g
        | TIff (R, R, f, g)
          -> aux g && strictly_relative_past f
        | TAnd (R, fs) -> aux (List.last_exn fs) && List.for_all (List.drop_last_exn fs) ~f:strictly_relative_past
        | TIff (_, _, f, g) -> aux f && aux g
        | TOr (_, fs) -> List.for_all fs ~f:aux
        | TSince (L, _, f, g) -> aux f && strictly_relative_past g
        | TSince (R, _, f, g) -> aux f && aux g
        | TUntil (R, _, _, f, g) -> aux f && strictly_relative_past g
        | TUntil (_, _, _, f, g) -> aux g && strictly_relative_past f
        | _ -> false
      end
    | _ -> assert false
  in
  aux f

let convert_transparently_enforceable pols f b pos =
  let f' = convert_enforceable pols f b pos in
  if is_transparent f' then
    f'
  else
    let err_msg = Printf.sprintf "The formula\n %s\nis not transparently enforceable."
                     (Formula.to_string f) in
    Util.type_error err_msg pos

(* TODO: type check formulas with information in pols *)
(* let type_trule pols = function *)
let type_trule _ = function
  | TSRule (pos, idx, label, type_fixes, rule, rule_type, rule_constrs, doc_string) -> begin
      let rule =  (*[FH] todo, filler code!*) 
        match rule with
        | TException (f1, refs, f2) -> 
           EException (List.map f1 ~f:(fun (p,f') -> (p, Tformula.of_formula f')), refs, Tformula.of_formula f2)
        | TScope (f1, refs, f2) -> 
           EScope (List.map f1 ~f:(fun (p,f') -> (p, Tformula.of_formula f')), refs, Tformula.of_formula f2)
        | TObligation (f1, f2) ->
           EObligation (List.map f1 ~f:(fun (p,f') -> (p, Tformula.of_formula f')), List.map f2 ~f:(fun (p,f') -> (p, Tformula.of_formula f')))
        | TPermission (f1, f2) ->
           EPermission (List.map f1 ~f:(fun (p,f') -> (p, Tformula.of_formula f')), List.map f2 ~f:(fun (p,f') -> (p, Tformula.of_formula f')))
        | TConstitutive (f1, f2) ->
           EConstitutive (List.map f1 ~f:(fun (p,f') -> (p, Tformula.of_formula f')), List.map f2 ~f:(fun (p,f') -> (p, Tformula.of_formula f')))
      in
      ESRule (pos, idx, label, type_fixes, rule, rule_type, rule_constrs, doc_string)
    end
  | _ -> assert false

let type_tstmt pols = function
  | TSImport (pos, idents, import_format) ->
     ESImport (pos, idents, import_format)
  | TSSection (section_kind, full_label, label, title) -> 
     ESSection (section_kind, full_label, label, title)
  | TSRule _ as trule -> type_trule pols trule
  | TSEvent (event_type, name, typed_args, pol, doc_string) ->
     ESEvent (event_type, name, typed_args, pol, doc_string)
  | TSType (name, typ, doc_string) -> ESType (name, typ, doc_string)
  | TSNote text -> ESNote text

let type_exception _ f = Tformula.of_formula f

let type_scope _ f = Tformula.of_formula f

(* let type_exceptions pol exceptions =
  List.map exceptions ~f:(type_exception pol)

let type_scopes pol scopes =
  List.map scopes ~f:(type_scope pol) *)

let do_type _ tprog =
  let pols = Tlex.pol_map tprog in
  {
    estmts     = List.map tprog.tstmts ~f:(type_tstmt pols);
    ealiases   = tprog.taliases;
    eevents    = tprog.tevents;
    variables  = tprog.variables;
    rule_tree  = tprog.rule_tree;
    exception_predicates = Map.map tprog.exception_predicates ~f:(type_exception pols);
    scope_predicates     = Map.map tprog.scope_predicates ~f:(type_scope pols);
  }

