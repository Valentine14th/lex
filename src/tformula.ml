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

module Term = struct
    
  type core_t =
    | TVar of string
    | TConst of Dom.t
    | TApp of string * (t list)
    | TUnop of Formula.Term.unop * t
    | TBinop of t * Formula.Term.binop * t

  and t = { trm: core_t; tt: TypeTerm.t }

  let rec to_formula_term_core = function
    | TVar v -> Formula.Term.Var v
    | TConst d -> Const d
    | TApp (f, trms) -> App (f, List.map trms ~f:to_formula_term)
    | TUnop (o, trm) -> Unop (o, to_formula_term trm)
    | TBinop (trm, o, trm') -> Binop (to_formula_term trm, o, to_formula_term trm')

  and to_formula_term t = to_formula_term_core t.trm

  let unvar = function
    | TVar x -> x
    | TConst _ -> raise (Invalid_argument "unvar is undefined for Consts")
    | TApp _ -> raise (Invalid_argument "unvar is undefined for Apps")
    | TUnop _ -> raise (Invalid_argument "unvar is undefined for Unops")
    | TBinop _ -> raise (Invalid_argument "unvar is undefined for Binops")

  let is_const = function
    | TConst _ -> true
    | _ -> false

  let unconst = function
    | TVar _ -> raise (Invalid_argument "unconst is undefined for Vars")
    | TConst c -> c
    | TApp _ -> raise (Invalid_argument "unconst is undefined for Apps")
    | TUnop _ -> raise (Invalid_argument "unconst is undefined for Unops")
    | TBinop _ -> raise (Invalid_argument "unconst is undefined for Binops")

  let rec fv_list_core = function
    | [] -> []
    | TVar x :: trms -> x :: fv_list_core trms
    | _ :: trms -> fv_list_core trms
  and fv_list trms = fv_list_core (List.map trms ~f:(fun t -> t.trm))

  let rec equal_core t t' = match t, t' with
    | TVar x, TVar x' -> String.equal x x'
    | TConst d, TConst d' -> Dom.equal d d'
    | TApp (f, ts), TApp (f', ts') ->
       String.equal f f' && (match List.map2 ts ts' ~f:equal with
                             | Ok e -> List.for_all e ~f:(fun x -> x)
                             | Unequal_lengths -> false)
    | TUnop (o, t), TUnop (o', t') -> Formula.Term.equal_unop o o' && equal t t'
    | TBinop (t1, o, t2), TBinop (t1', o', t2') ->
       equal t1 t1' && Formula.Term.equal_binop o o' && equal t2 t2'
    | _ -> false
  
  and equal t t' = equal_core t.trm t'.trm && TypeTerm.equal t.tt t'.tt

  let rec to_string_core = function
    | TVar x -> Printf.sprintf "TVar %s" x
    | TConst d -> Printf.sprintf "TConst %s" (Dom.to_string d)
    | TApp (f, ts) -> Printf.sprintf "TApp %s(%s)" f
                       (String.concat ~sep:", " (List.map ts ~f:to_string))
    | TUnop (o, t) -> Printf.sprintf "TUnop %s (%s)" (Formula.Term.string_of_unop o) (to_string t)
    | TBinop (t, o, t') -> Printf.sprintf "TBinop (%s) %s (%s)"
                             (to_string t) (Formula.Term.string_of_binop o) (to_string t')

  and to_string t = Printf.sprintf "%s : %s" (to_string_core t.trm) (TypeTerm.to_string t.tt)

  let rec value_to_string_core ?(l=0) = function
    | TVar x -> Printf.sprintf "%s" x
    | TConst d -> Printf.sprintf "%s" (Dom.to_string d)
    | TApp (f, trms) -> Printf.sprintf "%s(%s)" f (list_to_string trms)
    | TUnop (o, t) -> Printf.sprintf (Util.paren l 10 "%s %s")
                       (Formula.Term.string_of_unop o)
                       (value_to_string ~l:10 t)
    | TBinop (t, o, t') -> let l' = Formula.Term.prio_of_binop o in
                          Printf.sprintf (Util.paren l l' "%s %s %s")
                            (value_to_string ~l:l' t)
                            (Formula.Term.string_of_binop o)
                            (value_to_string ~l:l' t')
  and list_to_string trms = String.concat ~sep:", " (List.map trms ~f:value_to_string)
  
  and value_to_string ?(l=0) t = 
    Printf.sprintf (Util.paren l 0 "%a : %s")
      (fun _ -> value_to_string_core ~l:5) t.trm (TypeTerm.value_to_string t.tt)

  let rec untyped_value_to_string_core ?(l=0) = function
    | TVar x -> Printf.sprintf "%s" x
    | TConst d -> Printf.sprintf "%s" (Dom.to_string d)
    | TApp (f, trms) -> Printf.sprintf "%s(%s)" f (untyped_list_to_string trms)
    | TUnop (o, t) -> Printf.sprintf (Util.paren l 10 "%s %s")
                       (Formula.Term.string_of_unop o)
                       (untyped_value_to_string ~l:10 t)
    | TBinop (t, o, t') -> let l' = Formula.Term.prio_of_binop o in
                           Printf.sprintf (Util.paren l l' "%s %s %s")
                             (untyped_value_to_string ~l:l' t)
                             (Formula.Term.string_of_binop o)
                             (untyped_value_to_string ~l:l' t')
  and untyped_list_to_string trms = String.concat ~sep:", " (List.map trms ~f:untyped_value_to_string)
  
  and untyped_value_to_string ?(l=0) t = 
    Printf.sprintf (Util.paren l 0 "%a") (fun _ -> untyped_value_to_string_core ~l:5) t.trm

end

let term trm tt = Term.({ trm; tt })

type t =
  | TTT
  | TFF
  | TEqConst of Term.t * Term.t
  | TPredicate of string * Term.t list
  | TNeg of t
  | TAnd of Side.t * (t list)
  | TOr of Side.t * (t list)
  | TImp of Side.t * t * t
  | TIff of Side.t * Side.t * t * t
  | TExists of string * t
  | TForall of string * t
  | TPrev of Interval.t * t
  | TNext of Interval.t * t
  | TOnce of Interval.t * t
  | TEventually of Interval.t * t
  | THistorically of Interval.t * t
  | TAlways of Interval.t * t
  | TSince of Side.t * Interval.t * t * t
  | TUntil of Side.t * Interval.t * t * t
  | TType of t * ty

let ttt = TTT
let fff = TFF
let teqconst x d = TEqConst (x, d)
let tpredicate p_name trms = TPredicate (p_name, trms)
let tneg f = TNeg f
let tconj s f g = TAnd (s, [f; g])
let tdisj s f g = TOr (s, [f; g])
let timp s f g = TImp (s, f, g)
let tiff s t f g = TIff (s, t, f, g)
let texists x f = TExists (x, f)
let tforall x f = TForall (x, f)
let tprev i f = TPrev (i, f)
let tnext i f = TNext (i, f)
let tonce i f = TOnce (i, f)
let teventually i f = TEventually (i, f)
let thistorically i f = THistorically (i, f)
let talways i f = TAlways (i, f)
let tsince s i f g = TSince (s, i, f, g)
let tuntil s i f g = TUntil (s, i, f, g)
let ttype s t = TType (s, t)

let tbigcauconj = function
  | [] -> ttt
  | h::t -> List.fold_left t ~init:h ~f:(tconj N) (*TODO: assign correct type to formula, not just Non*)

let tbigcauforall vars f =
  List.fold_right vars ~init:f ~f:tforall 

let rec fv = function
  | TTT | TFF -> Set.empty (module String)
  | TEqConst (x, _) -> Set.of_list (module String) (Term.fv_list [x])
  | TPredicate (_, trms) -> Set.of_list (module String) (Term.fv_list trms)
  | TExists (x, f)
    | TForall (x, f) -> Set.filter (fv f) ~f:(fun y -> not (String.equal x y))
  | TNeg f
    | TPrev (_, f)
    | TOnce (_, f)
    | THistorically (_, f) 
    | TEventually (_, f)
    | TAlways (_, f)
    | TNext (_, f)
    | TType (f, _) -> fv f
    | TImp (_, f1, f2)
    | TIff (_, _, f1, f2)
    | TSince (_, _, f1, f2)
    | TUntil (_, _, f1, f2) -> Set.union (fv f1) (fv f2)
  | TAnd (_, fs)
    | TOr (_, fs) ->
     let f x g = Set.union x (fv g) in
     List.fold_left fs ~init:(Set.empty (module String)) ~f

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
    | TEventually (_, f)
    | THistorically (_, f)
    | TAlways (_, f)
    | TType (f, _) -> rank f
    | TImp (_, f, g)
    | TIff (_, _, f, g)
    | TSince (_, _, f, g)
    | TUntil (_, _, f, g) -> rank f + rank g
  | TAnd (_, fs)
    | TOr (_, fs) -> List.fold_left (List.map fs ~f:(fun f -> rank f)) ~init:0 ~f:(+)

let rec deg = function
  | TTT
    | TFF
    | TEqConst _ 
    | TPredicate _ -> 2
  | TNeg f 
    | TExists (_, f)
    | TForall (_, f)
    | TPrev (_, f)
    | TNext (_, f)
    | TOnce (_, f)
    | TEventually (_, f)
    | THistorically (_, f)
    | TAlways (_, f)
    | TType (f, _) -> deg f
    | TImp (_, f, g)
    | TIff (_, _, f, g)
    | TSince (_, _, f, g)
    | TUntil (_, _, f, g) -> max 2 (max (deg f) (deg g))
    | TAnd (_, fs)
    | TOr (_, fs) -> List.fold_left (List.map fs ~f:deg) ~init:1 ~f:max


let fix_side s f g =
  match s with
  | Side.LR -> if rank f < rank g then Side.L
               else Side.R
  | _ -> s

let rec to_formula = function
  | TTT -> TT
  | TFF -> FF
  | TEqConst (trm, trm') -> EqConst (Term.to_formula_term trm, Term.to_formula_term trm')
  | TPredicate (e, trms) -> Predicate (e, List.map trms ~f:Term.to_formula_term)
  | TNeg f -> Neg (to_formula f)
  | TAnd (s, fs) -> And (fix_side s (List.hd_exn fs) (List.last_exn fs),
                         List.map fs ~f:to_formula)
  | TOr (s, fs) -> Or (fix_side s (List.hd_exn fs) (List.last_exn fs),
                       List.map fs ~f:to_formula)
  | TImp (s, f, g) -> Imp (fix_side s f g, to_formula f, to_formula g)
  | TIff (s, t, f, g) -> Iff (fix_side s f g, fix_side t f g, to_formula f, to_formula g)
  | TExists (x, f) -> Exists (x, to_formula f)
  | TForall (x, f) -> Forall (x, to_formula f)
  | TPrev (i, f) -> Prev (i, to_formula f)
  | TNext (i, f) -> Next (i, to_formula f)
  | TOnce (i, f) -> Once (i, to_formula f)
  | TEventually (i, f) -> Eventually (i, to_formula f)
  | THistorically (i, f) -> Historically (i, to_formula f)
  | TAlways (i, f) -> Always (i, to_formula f)
  | TSince (s, i, f, g) -> Since (fix_side s f g, i, to_formula f, to_formula g)
  | TUntil (s, i, f, g) -> Until (s, i, to_formula f, to_formula g)
  | TType (f, ty) -> Type (to_formula f, ty)

let op_to_string = function
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst _ -> Printf.sprintf "="
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TNeg _ -> Printf.sprintf "¬"
  | TAnd (_, _) -> Printf.sprintf "∧"
  | TOr (_, _) -> Printf.sprintf "∨"
  | TImp (_, _, _) -> Printf.sprintf "→"
  | TIff (_, _, _, _) -> Printf.sprintf "↔"
  | TExists (x, _) -> Printf.sprintf "∃ %s." x
  | TForall (x, _) -> Printf.sprintf "∀ %s." x
  | TPrev (i, _) -> Printf.sprintf "●%s" (Interval.to_string i)
  | TNext (i, _) -> Printf.sprintf "○%s" (Interval.to_string i)
  | TOnce (i, _) -> Printf.sprintf "⧫%s" (Interval.to_string i)
  | TEventually (i, _) -> Printf.sprintf "◊%s" (Interval.to_string i)
  | THistorically (i, _) -> Printf.sprintf "■%s" (Interval.to_string i)
  | TAlways (i, _) -> Printf.sprintf "□%s" (Interval.to_string i)
  | TSince (_, i, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
  | TUntil (_, i,  _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
  | TType (_, _) -> Printf.sprintf ":"


let rec to_string_rec l = function
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst (trm, trm') -> Printf.sprintf "%s = %s" (Term.to_string trm) (Term.to_string trm')
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TNeg f -> Printf.sprintf "¬%a" (fun _ -> to_string_rec 5) f
  | TAnd (s, fs) ->
     let sep = "∧" ^ Side.to_string s in
     let strings = List.map fs ~f:(to_string_rec 4) in
     Util.paren_string l 4 (String.concat ~sep strings)
  | TOr (s, fs) ->
     let sep = "∨" ^ Side.to_string s in
     let strings = List.map fs ~f:(to_string_rec 4) in
     Util.paren_string l 3 (String.concat ~sep strings)
  | TImp (s, f, g) -> Printf.sprintf (Util.paren l 5 "%a →%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | TIff (s, t, f, g) -> Printf.sprintf (Util.paren l 5 "%a ↔%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string2) (s, t) (fun _ -> to_string_rec 5) g
  | TExists (x, f) -> Printf.sprintf (Util.paren l 5 "∃%s. %a") x (fun _ -> to_string_rec 5) f
  | TForall (x, f) -> Printf.sprintf (Util.paren l 5 "∀%s. %a") x (fun _ -> to_string_rec 5) f
  | TPrev (i, f) -> Printf.sprintf (Util.paren l 5 "●%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TNext (i, f) -> Printf.sprintf (Util.paren l 5 "○%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TOnce (i, f) -> Printf.sprintf (Util.paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TEventually (i, f) -> Printf.sprintf (Util.paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | THistorically (i, f) -> Printf.sprintf (Util.paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TAlways (i, f) -> Printf.sprintf (Util.paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | TSince (s, i, f, g) -> Printf.sprintf (Util.paren l 0 "%a S%a%a %a") (fun _ -> to_string_rec 5) f
                         (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | TUntil (s, i, f, g) -> Printf.sprintf (Util.paren l 0 "%a U%a%a %a") (fun _ -> to_string_rec 5) f
                             (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | TType (f, ty) -> Printf.sprintf (Util.paren l 0 "%a : %a") (fun _ -> to_string_rec 5) f (fun _ -> ty_to_string) ty


let to_string = to_string_rec 0

