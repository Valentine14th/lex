open Core

type core_t =
  | TT
  | FF
  | Term of Term.t
  | Predicate of string * Term.t list
  | Agg of string * Aggregation.op * Term.t * string list * t
  | Neg of t
  | And of Side.t * (t list)
  | Or of Side.t * (t list)
  | Imp of Side.t * t * t
  | Iff of (Side.t * Side.t) * t * t
  | Exists of string * t
  | Forall of string * t
  | Prev of Interval.t * t
  | Next of Interval.t * t
  | Once of Interval.t * t
  | Eventually of Interval.t * t
  | Historically of Interval.t * t
  | Always of Interval.t * t
  | Since of Side.t * Interval.t * t * t
  | Until of Side.t * Interval.t * t * t
  | Type of t * EnfType.t

and t = {
  f: core_t;
  variable_instantiations: (string * Term.t) list;
  pos: LexingInfo.t
}

let make_formula f instantiations pos = {f=f; variable_instantiations=instantiations; pos}

(* TODO: pass add parameter for variable instatntiations in order to correctly convert to Formula.t (for now instantiations are not acutally used in tformulas)*)
let tt pos = make_formula TT [] pos
let ff pos = make_formula FF [] pos
let term pos trm = make_formula (Term trm) [] pos
let agg pos s op x y f = make_formula (Agg (s, op, x, y, f)) [] pos
let predicate pos p_name trms = make_formula (Predicate (p_name, trms)) [] pos
let neg pos f = make_formula (Neg f) [] pos
let conj pos s f g = make_formula (And (s, [f; g])) [] pos
let disj pos s f g = make_formula (Or (s, [f; g])) [] pos
let conj' pos s fs = make_formula (And (s, fs)) [] pos
let disj' pos s fs = make_formula (Or (s, fs)) [] pos
let imp pos s f g = make_formula (Imp (s, f, g)) [] pos
let iff pos s2 f g = make_formula (Iff (s2, f, g)) [] pos
let exists pos x f = make_formula (Exists (x, f)) [] pos
let exists_list pos xs f = List.fold_right xs ~init:f ~f:(exists pos)
let forall pos x f = make_formula (Forall (x, f)) [] pos
let forall_list pos xs f = List.fold_right xs ~init:f ~f:(forall pos)
let prev pos i f = make_formula (Prev (i, f)) [] pos
let next pos i f = make_formula (Next (i, f)) [] pos
let once pos i f = make_formula (Once (i, f)) [] pos
let eventually pos i f = make_formula (Eventually (i, f)) [] pos
let historically pos i f = make_formula (Historically (i, f)) [] pos
let always pos i f = make_formula (Always (i, f)) [] pos
let since pos s i f g = make_formula (Since (s, i, f, g)) [] pos
let until pos s i f g = make_formula (Until (s, i, f, g)) [] pos
let type_ pos s t = make_formula (Type (s, t)) [] pos

(* Rewriting of non-native operators *)
let trigger pos s i f g = neg pos (since f.pos s i (neg f.pos f) (neg g.pos g))
let release pos s i f g = neg pos (until f.pos s i (neg f.pos f) (neg g.pos g))

let rec init (sf: Sformula.t) : t = match sf.f with
  | SConst (Dom.Bool true) -> tt sf.pos
  | SConst (Dom.Bool false) -> ff sf.pos
  | SApp (s, sfs) -> predicate sf.pos s (List.map sfs ~f:init_term)
  | SAgg (s, op, x, y, f) -> agg sf.pos s op (init_term x) y (init f)
  | SBop (None, f, op, g) when Sformula.Bop.is_relational op ->
     begin
       let binop = match op with
         | Sformula.Bop.BEq -> Term.BEq
         | BNeq -> BNeq
         | BLt -> BLt
         | BLeq -> BLeq
         | BGt -> BGt
         | BGeq -> BGeq
         | _ -> assert false in
       term sf.pos (Term.binop sf.pos (init_term f) binop (init_term g))
     end
  | SBop (s_opt, f, op, g) ->
     begin
       match op with
       | Sformula.Bop.BAnd -> conj sf.pos (Side.value s_opt) (init f) (init g)
       | BOr -> disj sf.pos (Side.value s_opt) (init f) (init g)
       | BImp -> imp sf.pos (Side.value s_opt) (init f) (init g)
       | _ -> assert false
     end
  | SBop2 (s2_opt, f, op, g) ->
     begin
       match op with
       | Sformula.Bop2.BIff -> iff sf.pos (Side.value2 s2_opt) (init f) (init g)
     end
  | SUop (op, f) ->
     begin
       match op with
       | Sformula.Uop.UNot -> neg sf.pos (init f)
       | _ -> assert false
     end
  | SExists (xs, f) -> exists_list sf.pos xs (init f)
  | SForall (xs, f) -> forall_list sf.pos xs (init f)
  | SBtop (s_opt, i, f, btop, g) ->
     begin
       match btop with
       | Sformula.Btop.BSince -> since sf.pos (Side.value s_opt) i (init f) (init g)
       | BUntil -> until sf.pos (Side.value s_opt) i (init f) (init g)
       | BRelease -> release sf.pos (Side.value s_opt) i (init f) (init g)
       | BTrigger -> trigger sf.pos (Side.value s_opt) i (init f) (init g)
     end
  | SUtop (i, utop, f) ->
     begin
       match utop with
       | Sformula.Utop.UNext -> next sf.pos i (init f)
       | UPrev -> prev sf.pos i (init f)
       | UAlways -> always sf.pos i (init f)
       | UHistorically -> historically sf.pos i (init f)
       | UEventually -> eventually sf.pos i (init f)
       | UOnce -> once sf.pos i (init f)
     end
  | _ -> assert false

and init_term (sf: Sformula.t) : Term.t = match sf.f with
  | SConst c -> Term.const sf.pos c
  | SVar s -> Term.var sf.pos s
  | SApp (s, sfs) -> Term.app sf.pos s (List.map sfs ~f:init_term)
  | SBop (None, f, op, g) ->
     begin
      let binop = match op with
        | Sformula.Bop.BAnd -> Term.BAnd
        | BOr -> BOr
        | BAdd -> BAdd
        | BSub -> BSub
        | BMul -> BMul
        | BDiv -> BDiv
        | BPow -> BPow
        | BEq -> BEq
        | BNeq -> BNeq
        | BLt -> BLt
        | BLeq -> BLeq
        | BGt -> BGt
        | BGeq -> BGeq
        | _ -> assert false in
      Term.binop sf.pos (init_term f) binop (init_term g)
     end
  | SUop (op, f) ->
     begin
       let unop = match op with
         | Sformula.Uop.USub -> Term.USub
         | UNot -> UNot
       in
       Term.unop sf.pos unop (init_term f)
     end
  | _ -> assert false

let rec fv (f: t) = match f.f with
  | TT | FF -> Set.empty (module String)
  | Term trm -> Set.of_list (module String) (Term.fv_list [trm])
  | Predicate (_, trms) -> Set.of_list (module String) (Term.fv_list trms)
  | Agg (s, _, _, y, _) -> Set.of_list (module String) (s :: y)
  | Exists (x, f)
    | Forall (x, f) -> Set.filter (fv f) ~f:(fun y -> not (String.equal x y))
  | Neg g
    | Prev (_, g)
    | Once (_, g)
    | Historically (_, g)
    | Eventually (_, g)
    | Always (_, g)
    | Next (_, g)
    | Type (g, _) -> fv g
  | Imp (_, f1, f2)
    | Iff (_, f1, f2)
    | Since (_, _, f1, f2)
    | Until (_, _, f1, f2) -> Set.union (fv f1) (fv f2)
  | And (_, fs)
    | Or (_, fs) ->
     let f x g = Set.union x (fv g) in
     List.fold_left fs ~init:(Set.empty (module String)) ~f

let rec deg f = match f.f with
  | TT
    | FF
    | Term _ 
    | Predicate _ -> 2
  | Neg f 
    | Exists (_, f)
    | Forall (_, f)
    | Prev (_, f)
    | Next (_, f)
    | Once (_, f)
    | Eventually (_, f)
    | Historically (_, f)
    | Always (_, f)
    | Type (f, _)
    | Agg (_, _, _, _, f) -> deg f
    | Imp (_, f, g)
    | Iff (_, f, g)
    | Since (_, _, f, g)
    | Until (_, _, f, g) -> max 2 (max (deg f) (deg g))
    | And (_, fs)
    | Or (_, fs) -> List.fold_left (List.map fs ~f:deg) ~init:1 ~f:max

let rec collect_predicates l f = match f.f with
  | TT
    | FF
    | Term _ -> l
  | Predicate (r, trms) -> (r, trms) :: l
  | Neg f 
    | Exists (_, f)
    | Forall (_, f)
    | Prev (_, f)
    | Next (_, f)
    | Once (_, f)
    | Eventually (_, f)
    | Historically (_, f)
    | Always(_, f)
    | Agg (_, _, _, _, f) -> collect_predicates l f
    | Imp (_, f, g)
    | Iff (_, f, g)
    | Since (_, _, f, g)
    | Until (_, _, f, g) -> collect_predicates (collect_predicates l f) g
  | Type (f, _) -> collect_predicates l f
  | And (_, fs)
    | Or (_, fs) -> List.fold_left fs ~init:l ~f:collect_predicates

let rec flatten_assoc f = match f.f with
  | TT | FF | Term _ | Predicate _ -> f
  | Agg (s, op, x, y, f) -> agg f.pos s op x y (flatten_assoc f)
  | Neg f -> neg f.pos (flatten_assoc f)
  | Exists (x, g) -> exists f.pos x (flatten_assoc g)
  | Forall (x, g) -> forall f.pos x (flatten_assoc g)
  | Prev (i, g) -> prev f.pos i (flatten_assoc g)
  | Next (i, g) -> next f.pos i (flatten_assoc g)
  | Once (i, g) -> once f.pos i (flatten_assoc g)
  | Eventually (i, g) -> eventually f.pos i (flatten_assoc g)
  | Historically (i, g) -> historically f.pos i (flatten_assoc g)
  | Always(i, g) -> always f.pos i (flatten_assoc g)
  | Imp (s, g, h) -> imp f.pos s (flatten_assoc g) (flatten_assoc h)
  | Iff (s, g, h) -> iff f.pos s (flatten_assoc g) (flatten_assoc h)
  | Since (s, i, g, h) -> since f.pos s i (flatten_assoc g) (flatten_assoc h)
  | Until (s, i, g, h) -> until f.pos s i (flatten_assoc g) (flatten_assoc h)
  | Type (g, ty) -> type_ f.pos (flatten_assoc g) ty
  | And (s, gs) when Side.equal s L || Side.equal s N ->
    conj' f.pos s (List.concat (List.map gs ~f:(fun g -> match g.f with And (_, gs) -> gs | _ -> [g])))
  | And (s, gs) -> conj' f.pos s (List.map gs ~f:flatten_assoc)
  | Or (s, gs) when Side.equal s L || Side.equal s N ->
    disj' f.pos s (List.concat (List.map gs ~f:(fun g -> match g.f with Or (_, gs) -> gs | _ -> [g])))
  | Or (s, gs) -> disj' f.pos s (List.map gs ~f:flatten_assoc)


let rec string_of_instantiations = function
  | [] -> ""
  | [(x, t)] -> Printf.sprintf "%s <- %s" x (Term.value_to_string t)
  | (x, t) :: insts ->  Printf.sprintf "%s <- %s, %s" x (Term.value_to_string t) (string_of_instantiations insts)


let rec to_string_core_rec l (f: t) = match f.f with
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | Term trm -> Printf.sprintf "(%s)" (Term.value_to_string trm) 
  | Predicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | Agg (s, op, x, y, f) -> Printf.sprintf "%s = %s(%s; %s; %s)" s (Aggregation.op_to_string op) (Term.value_to_string x) (String.concat ~sep:", " y) (to_string_rec 5 f)
  | Neg f -> Printf.sprintf "¬%a" (fun _ -> to_string_rec 5) f
  | And (s, fs) ->
     let sep = Printf.sprintf " ∧%s " (Side.to_string s) in
     let strings = List.map fs ~f:(to_string_rec 4) in
     Util.paren_string l 4 (String.concat ~sep strings)
  | Or (s, fs) ->
     let sep = Printf.sprintf " ∨%s " (Side.to_string s) in
     let strings = List.map fs ~f:(to_string_rec 4) in
     Util.paren_string l 3 (String.concat ~sep strings)
  | Imp (s, f, g) -> Printf.sprintf (Util.paren l 5 "%a →%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | Iff (s, f, g) -> Printf.sprintf (Util.paren l 5 "%a ↔%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string2) s (fun _ -> to_string_rec 5) g
  | Exists (x, f) -> Printf.sprintf (Util.paren l 5 "∃%s. %a") x (fun _ -> to_string_rec 5) f
  | Forall (x, f) -> Printf.sprintf (Util.paren l 5 "∀%s. %a") x (fun _ -> to_string_rec 5) f
  | Prev (i, f) -> Printf.sprintf (Util.paren l 5 "●%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Next (i, f) -> Printf.sprintf (Util.paren l 5 "○%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Once (i, f) -> Printf.sprintf (Util.paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Eventually (i, f) -> Printf.sprintf (Util.paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Historically (i, f) -> Printf.sprintf (Util.paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Always (i, f) -> Printf.sprintf (Util.paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Since (s, i, f, g) -> Printf.sprintf (Util.paren l 0 "%a S%a%a %a") (fun _ -> to_string_rec 5) f
                          (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | Until (s, i, f, g) -> Printf.sprintf (Util.paren l 0 "%a U%a%a %a") (fun _ -> to_string_rec 5) f
                            (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | Type (f, t) -> Printf.sprintf (Util.paren l 0 "%a : %a") (fun _ -> to_string_rec 5) f
                            (fun _ -> EnfType.to_string) t
and to_string_rec l f =
  let f_str = to_string_core_rec l f in
  match f.variable_instantiations with
  | [] -> f_str
  | _ -> Printf.sprintf "(%s; %s)" f_str (string_of_instantiations f.variable_instantiations)


let to_string = to_string_rec 0
