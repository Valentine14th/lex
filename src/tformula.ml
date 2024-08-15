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

module TTerm = struct
    
  type core_t =
    | TVar of string
    | TConst of Dom.t
    | TApp of string * (t list)
    | TUnop of Formula.Term.unop * t
    | TBinop of t * Formula.Term.binop * t
    | TProj of t * string
    | TRecord of (string * t) list
  and t = { trm: core_t; tt: TypeTerm.t; positions: Lexing.position list }

  let rec to_formula_term_core = function
    | TVar v -> Term.Var v
    | TConst d -> Term.Const d
    | TApp (f, trms) -> Term.App (f, List.map trms ~f:to_formula_term)
    | TUnop (o, trm) -> Term.Unop (o, to_formula_term trm)
    | TBinop (trm, o, trm') -> Term.Binop (to_formula_term trm, o, to_formula_term trm')
    | TProj (trm, p) -> Term.Proj (to_formula_term trm, p)
    | TRecord kvs -> Term.Record (List.map ~f:(fun (k, v) -> (k, to_formula_term v)) kvs)

  and to_formula_term (t: t): Formula.Term.t = Term.make_term (to_formula_term_core t.trm) t.positions

  let unvar = function
    | TVar x -> x
    | TConst _ -> raise (Invalid_argument "unvar is undefined for Consts")
    | TApp _ -> raise (Invalid_argument "unvar is undefined for Apps")
    | TUnop _ -> raise (Invalid_argument "unvar is undefined for Unops")
    | TBinop _ -> raise (Invalid_argument "unvar is undefined for Binops")
    | TProj _ -> raise (Invalid_argument "unvar is undefined for Projs")
    | TRecord _ -> raise (Invalid_argument "unvar is undefined for Records")

  let is_const = function
    | TConst _ -> true
    | _ -> false

  let unconst = function
    | TVar _ -> raise (Invalid_argument "unconst is undefined for Vars")
    | TConst c -> c
    | TApp _ -> raise (Invalid_argument "unconst is undefined for Apps")
    | TUnop _ -> raise (Invalid_argument "unconst is undefined for Unops")
    | TBinop _ -> raise (Invalid_argument "unconst is undefined for Binops")
    | TProj _ -> raise (Invalid_argument "unconst is undefined for Projs")
    | TRecord _ -> raise (Invalid_argument "unconst is undefined for Records")

  let rec fv_list_core = function
    | [] -> []
    | (TVar x, positions) :: trms -> (x, positions) :: fv_list_core trms
    | _ :: trms -> fv_list_core trms

  and fv_list trms = fv_list_core (List.map trms ~f:(fun t -> t.trm, t.positions))

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
    | TProj (t, p) -> Printf.sprintf "Proj (%s).%s" (to_string t) p
    | TRecord kvs ->
       Printf.sprintf "Record { %s }"
         (String.concat ~sep:", " (List.map kvs ~f:(fun (k, v) -> k ^ " : " ^ to_string v)))


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
    | TProj (t, p) -> Printf.sprintf "%s.%s" (value_to_string ~l:10 t) p
    | TRecord kvs ->
       let f (k, v) = k ^ " : " ^ value_to_string v in
       Printf.sprintf "{ %s }" (String.concat ~sep:", " (List.map kvs ~f))

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
    | TProj (t, p) -> Printf.sprintf "%s.%s" (untyped_value_to_string ~l:10 t) p
    | TRecord kvs ->
       let f (k, v) = k ^ " : " ^ untyped_value_to_string v in
       Printf.sprintf "{ %s }" (String.concat ~sep:", " (List.map kvs ~f))

  and untyped_list_to_string trms = String.concat ~sep:", " (List.map trms ~f:untyped_value_to_string)
  
  and untyped_value_to_string ?(l=0) t = 
    Printf.sprintf (Util.paren l 0 "%a") (fun _ -> untyped_value_to_string_core ~l:5) t.trm

end

let tterm trm tt positions = TTerm.({ trm; tt; positions })

type core_t =
  | TTT
  | TFF
  | TEqConst of TTerm.t * TTerm.t
  | TPredicate of string * TTerm.t list * Lex.event_type
  | TAgg of string * Aggregation.op * TTerm.t * string list * t
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

and t = {f: core_t; positions: Lexing.position list}

let make_tformula f pos = {f=f; positions=pos}

let ttt pos = make_tformula TTT pos
let tff pos = make_tformula TFF pos
let teqconst pos x d = make_tformula (TEqConst (x, d)) pos
let tpredicate pos p_name trms event_type = make_tformula (TPredicate (p_name, trms, event_type)) pos
let tagg pos u op x y f = make_tformula (TAgg (u, op, x, y, f)) pos
let tneg pos f = make_tformula (TNeg f) pos
let tconj pos s f g = make_tformula (TAnd (s, [f; g])) pos
let tdisj pos s f g = make_tformula (TOr (s, [f; g])) pos
let tconj' pos s fs = make_tformula (TAnd (s, fs)) pos
let tdisj' pos s fs = make_tformula (TOr (s, fs)) pos
let timp pos s f g = make_tformula (TImp (s, f, g)) pos
let tiff pos s t f g = make_tformula (TIff (s, t, f, g)) pos
let texists pos x f = make_tformula (TExists (x, f)) pos
let tforall pos x f = make_tformula (TForall (x, f)) pos
let tprev pos i f = make_tformula (TPrev (i, f)) pos
let tnext pos i f = make_tformula (TNext (i, f)) pos
let tonce pos i f = make_tformula (TOnce (i, f)) pos
let teventually pos i f = make_tformula (TEventually (i, f)) pos
let thistorically pos i f = make_tformula (THistorically (i, f)) pos
let talways pos i f = make_tformula (TAlways (i, f)) pos
let tsince pos s i f g = make_tformula (TSince (s, i, f, g)) pos
let tuntil pos s i f g = make_tformula (TUntil (s, i, f, g)) pos
let ttype pos s t = make_tformula (TType (s, t)) pos

let tbigcauconj pos = function
  | [] -> ttt pos
  | h::t -> List.fold_left t ~init:h ~f:(tconj pos N) (*TODO: assign correct type to formula, not just Non*)

let tbigcauforall pos vars f =
  List.fold_right vars ~init:f ~f:(tforall pos)

module StringMap = Map.Make(String)

let rec fv map f =
  let aux0 v map p = Map.add_multi map ~key:v ~data:p in
  let aux1 map (v, ps) = List.fold ps ~init:map ~f:(aux0 v) in
  let merge_fun ~key:_ = function
    | `Left x | `Right x -> Some x
    | `Both (x, y) -> Some (x @ y)
  in
  let merge map1 map2 = Map.merge map1 map2  ~f:merge_fun in
  match f.f with
  | TTT | TFF -> map
  | TEqConst (x, _) ->
    TTerm.fv_list [x] |> List.fold ~init:map ~f:aux1
  | TPredicate (_, trms, _) -> 
    TTerm.fv_list trms |> List.fold ~init:map ~f:aux1
  | TAgg (s, _, _, ys, _) ->
    ((s, f.positions) :: List.map ys ~f:(fun y -> (y, f.positions)))
    |> List.fold ~init:map ~f:aux1
  | TExists (x, g)
    | TForall (x, g) ->
      Map.filter_keys (fv (Map.empty (module String)) g) ~f:(fun y -> not (String.equal x y))
      |> merge map (* merge with original map - doing it this way, instead of passing the map as an argument to fv above, we can avoid filtering out variables that are bound inside the quantifier, but free outside of it *)
  | TNeg g
    | TPrev (_, g)
    | TOnce (_, g)
    | THistorically (_, g) 
    | TEventually (_, g)
    | TAlways (_, g)
    | TNext (_, g)
    | TType (g, _) -> fv map g
    | TImp (_, f1, f2)
    | TIff (_, _, f1, f2)
    | TSince (_, _, f1, f2)
    | TUntil (_, _, f1, f2) -> fv (fv map f2) f1
  | TAnd (_, fs)
    | TOr (_, fs) ->
      List.fold_left fs ~init:map ~f:fv

let rec rank f = match f.f with
  | TTT | TFF -> 0
  | TEqConst _ -> 0
  | TPredicate (_, args, _) -> List.length args
  | TNeg f
    | TExists (_, f)
    | TForall (_, f)
    | TPrev (_, f)
    | TNext (_, f)
    | TOnce (_, f)
    | TEventually (_, f)
    | THistorically (_, f)
    | TAlways (_, f)
    | TType (f, _)
    | TAgg (_, _, _, _, f) -> rank f
    | TImp (_, f, g)
    | TIff (_, _, f, g)
    | TSince (_, _, f, g)
    | TUntil (_, _, f, g) -> rank f + rank g
  | TAnd (_, fs)
    | TOr (_, fs) -> List.fold_left (List.map fs ~f:(fun f -> rank f)) ~init:0 ~f:(+)

let rec deg f = match f.f with
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
    | TType (f, _)
    | TAgg (_, _, _, _, f) -> deg f
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

let rec to_formula (f: t): Formula.t = match f.f with
  | TTT -> tt f.positions
  | TFF -> ff f.positions
  | TEqConst (trm, trm') ->
    term f.positions (Term.binop f.positions (TTerm.to_formula_term trm) Formula.Term.BEq (TTerm.to_formula_term trm'))
  | TPredicate (e, trms, _) -> predicate f.positions e (List.map trms ~f:TTerm.to_formula_term)
  | TAgg (s, op, x, y, g) -> agg f.positions s op (TTerm.to_formula_term x) y (to_formula g)
  | TNeg g -> neg f.positions (to_formula g)
  | TAnd (s, fs) -> conj' f.positions (fix_side s (List.hd_exn fs) (List.last_exn fs)) (List.map fs ~f:to_formula)
  | TOr (s, fs) -> disj' f.positions (fix_side s (List.hd_exn fs) (List.last_exn fs)) (List.map fs ~f:to_formula)
  | TImp (s, g, h) -> imp f.positions (fix_side s g h) (to_formula g) (to_formula h)
  | TIff (s, t, g, h) -> iff f.positions (fix_side s g h) (fix_side t g h) (to_formula g) (to_formula h)
  | TExists (x, g) -> exists f.positions x (to_formula g)
  | TForall (x, g) -> forall f.positions x (to_formula g)
  | TPrev (i, g) -> prev f.positions i (to_formula g)
  | TNext (i, g) -> next f.positions i (to_formula g)
  | TOnce (i, g) -> once f.positions i (to_formula g)
  | TEventually (i, g) -> eventually f.positions i (to_formula g)
  | THistorically (i, g) -> historically f.positions i (to_formula g)
  | TAlways (i, g) -> always f.positions i (to_formula g)
  | TSince (s, i, g, h) -> since f.positions (fix_side s g h) i (to_formula g) (to_formula h)
  | TUntil (s, i, g, h) -> until f.positions s i (to_formula g) (to_formula h)
  | TType (g, ty) -> type_ f.positions (to_formula g) ty

let op_to_string f = match f.f with
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst _ -> Printf.sprintf "="
  | TPredicate (r, trms, _) -> Printf.sprintf "%s(%s)" r (TTerm.list_to_string trms)
  | TAgg (_, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" (Aggregation.op_to_string op) (TTerm.value_to_string x) (String.concat ~sep:", " y)
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


let rec to_string_rec l f = match f.f with
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst (trm, trm') -> Printf.sprintf "%s = %s" (TTerm.to_string trm) (TTerm.to_string trm')
  | TAgg (s, op, x, y, f) -> Printf.sprintf "%s = %s(%s; %s; %s)" s (Aggregation.op_to_string op) (TTerm.value_to_string x) (String.concat ~sep:", " y) (to_string_rec 5 f)
  | TPredicate (r, trms, _) -> Printf.sprintf "%s(%s)" r (TTerm.list_to_string trms)
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

let rec collect_tpredicates l f = match f.f with
  | TTT
  | TFF
  | TEqConst _ 
  | TType _
    | TAgg _ -> l
  | TPredicate (name, terms, t) -> (name, terms, t) :: l
  | TAnd (_, fs)
    | TOr (_, fs) -> List.fold fs ~init:l ~f:collect_tpredicates
  | TNeg f
  | TExists (_, f)
  | TForall (_, f)
  | TPrev (_, f)
  | TNext (_, f)
  | TOnce (_, f)
  | TEventually (_, f)
  | THistorically (_, f)
    | TAlways (_, f) -> collect_tpredicates l f
  | TImp (_, f, g)
  | TIff (_, _, f, g)
  | TSince (_, _, f, g)
    | TUntil (_, _, f, g) -> collect_tpredicates (collect_tpredicates l f) g

let to_string = to_string_rec 0

let rec relative_interval ?(itl_itvs=Map.empty (module String)) (f: t): Zinterval.t =
  let relative_interval = relative_interval ~itl_itvs:itl_itvs in
  match f.f with
  | TTT | TFF | TEqConst _ -> Zinterval.singleton 0
  | TPredicate (n, _, _) ->
    begin match Map.find itl_itvs n with
      | Some i -> i
      | None -> Zinterval.singleton 0
    end
  | TAgg (_, _, _, _, f) -> Zinterval.to_zero (relative_interval f)
  | TNeg f | TExists (_, f) | TForall (_, f) -> relative_interval f
  | TAnd (_, fs) | TOr (_, fs)
    -> List.fold_left (List.map fs ~f:relative_interval) ~init:Zinterval.full ~f:Zinterval.lub
  | TImp (_, f1, f2) | TIff (_, _, f1, f2)
    -> Zinterval.lub (relative_interval f1) (relative_interval f2)
  | TPrev (i, f) | TOnce (i, f) | THistorically (i, f)
    -> let i' = Zinterval.inv (Zinterval.of_interval i) in
       Zinterval.lub (Zinterval.to_zero i') (Zinterval.sum i' (relative_interval f))
  | TNext (i, f) | TEventually (i, f) | TAlways (i, f)
    -> let i = Zinterval.of_interval i in
       Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i (relative_interval f))
  | TSince (_, i, f1, f2) ->
     let i' = Zinterval.inv (Zinterval.of_interval i) in
     (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
        (Zinterval.sum i' (relative_interval f2)))
  | TUntil (_, i, f1, f2) ->
     let i' = Zinterval.of_interval i in
     (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
        (Zinterval.sum i' (relative_interval f2)))
  | TType (f, _) -> relative_interval f

let strict ?(itl_strict=Map.empty (module String)) ?(itv=Zinterval.singleton 0) ?(fut=false) (f: t) =
  let rec _strict itv fut (f: t) =
    ((Zinterval.mem 0 itv) && fut)
    || (match f.f with
        | TTT | TFF | TEqConst (_, _) -> false
        | TPredicate (name, _, _) ->
          begin match Map.find itl_strict name with
            | Some b -> not b
            | None -> false
          end
        | TNeg f | TExists (_, f) | TForall (_, f) | TAgg (_, _, _, _, f) -> _strict itv fut f
        | TImp (_, f1, f2) | TIff (_, _, f1, f2)
          -> (_strict itv fut f1) || (_strict itv fut f2)
        | TAnd (_, fs) | TOr (_, fs)
          -> List.exists fs ~f:(_strict itv fut)
        | TPrev (i, f) | TOnce (i, f) | THistorically (i, f)
          -> _strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f
        | TNext (i, f) | TEventually (i, f) | TAlways (i, f)
          -> _strict (Zinterval.sum (Zinterval.of_interval i) itv) true f
        | TSince (_, i, f1, f2)
          -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f1)
             || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f2)
        | TUntil (_, i, f1, f2)
          -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f1)
             || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f2)
        | TType (f, _) -> _strict itv fut f)
  in not (_strict itv fut f)

let relative_past ?(itl_itvs=Map.empty (module String)) (f: t): bool =
  Zinterval.is_nonpositive (relative_interval ~itl_itvs:itl_itvs f)

let strictly_relative_past ?(itl_itvs_and_strict=Map.empty (module String), Map.empty (module String)) (f: t): bool =
  (relative_past ~itl_itvs:(fst itl_itvs_and_strict) f) && (strict ~itl_strict:(snd itl_itvs_and_strict) f)

let get_predicate_name f = match f.f with
  | TPredicate (n,_,_) -> n
  | _ -> assert false
let get_predicate_params f = match f.f with
  | TPredicate (_,ts,_) -> ts
  | _ -> assert false

let rec is_transparent (t: EnfType.t) (f: t) =
  let is_transparent = is_transparent t in
  match t with
  | Cau -> begin
    match f.f with
      | TTT | TPredicate _ -> true
      | TNeg f | TExists (_, f) | TForall (_, f)
        | TOnce (_, f) | TNext (_, f) | THistorically (_, f)
          | TAlways (_, f) -> is_transparent f
      | TEventually (i, f) -> Interval.is_bounded i && is_transparent f
      | TImp (L, f, g) | TIff (L, L, f, g) -> is_transparent f && strictly_relative_past g
      | TOr (L, f :: fs) -> is_transparent f && List.for_all fs ~f:strictly_relative_past
      | TImp (R, f, g) | TIff (R, R, f, g) -> is_transparent g && strictly_relative_past f
      | TOr (R, fs) -> is_transparent (List.last_exn fs) && List.for_all (List.drop_last_exn fs) ~f:strictly_relative_past
      | TAnd (_, fs) -> List.for_all fs ~f:is_transparent
      | TIff (_, _, f, g) -> is_transparent f && is_transparent g
      | TSince (_, _, f, g) -> is_transparent f && strictly_relative_past g
      | TUntil (R, i, f, g) -> Interval.is_bounded i && is_transparent f && strictly_relative_past g
      | TUntil (LR, i, f, g) -> Interval.is_bounded i && is_transparent f && is_transparent g
      | _ -> false
    end
  | Sup -> begin
    match f.f with
      | TFF | TPredicate _ -> true
      | TNeg f | TExists (_, f) | TForall (_, f)
        | TOnce (_, f) | TNext (_, f) | THistorically (_, f)
        | TEventually (_, f) -> is_transparent f
      | TAlways (i, f) -> Interval.is_bounded i && is_transparent f
      | TAnd (L, f :: fs) -> is_transparent f && List.for_all fs ~f:strictly_relative_past
      | TIff (L, L, f, g) -> is_transparent f && strictly_relative_past g
      | TIff (R, R, f, g) -> is_transparent g && strictly_relative_past f
      | TAnd (R, fs) -> is_transparent (List.last_exn fs) && List.for_all (List.drop_last_exn fs) ~f:strictly_relative_past
      | TIff (_, _, f, g) -> is_transparent f && is_transparent g
      | TOr (_, fs) -> List.for_all fs ~f:is_transparent
      | TSince (L, _, f, g) -> is_transparent f && strictly_relative_past g
      | TSince (R, _, f, g) -> is_transparent f && is_transparent g
      | TUntil (R, _, f, g) -> is_transparent f && strictly_relative_past g
      | TUntil (_, _, f, g) -> is_transparent g && strictly_relative_past f
      | _ -> false
    end
  | _ -> assert false

