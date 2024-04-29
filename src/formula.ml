open Core

module EnfType = struct

  type t = Non | Cau | Obs | Sup | CauObs | CauSup | Itl [@@deriving compare, sexp_of, hash]
  
  let to_string = function
    | Non    -> ""
    | Cau    -> "causable"
    | Obs    -> "observable"
    | Sup    -> "suppressable"
    | CauObs -> "causable observable"
    | CauSup -> "causable suppressable"
    | Itl    -> "internal"

  let equal a b = match a, b with
    | Cau, Cau -> true
    | Sup, Sup -> true
    | CauSup, CauSup -> true
    | Obs, Obs -> true
    | _, _ -> false

  let meet a b = match a, b with
    | _, _ when equal a b -> a
    | Cau, Sup | Sup, Cau | CauSup, _ | _, CauSup -> CauSup
    | Obs, x | x, Obs -> x
    | _, _ -> Obs

  let join a b = match a, b with
    | _, _ when equal a b -> a
    | Cau, Sup | Sup, Cau | Obs, _ | _, Obs -> Obs
    | Cau, _ | _, Cau -> Cau
    | _, _ -> Sup

  let leq a b = equal (join a b) a
  let geq a b = equal (meet a b) b

  let specialize a b = if leq b a then Some b else None

end


module Side = struct

  type t = N | L | R | LR

  let equal s s' = match s, s' with
    | N, N | L, L | R, R | LR, LR -> true
    | _ -> false

  let to_string = function
    | N  -> ""
    | L  -> ":L"
    | R  -> ":R"
    | LR -> ":LR"

  let to_string2 =
    let aux = function N  -> "N" | L  -> "L" | R  -> "R" | LR -> "LR"
    in function (N, N) -> "" | (a, b) -> ":" ^ aux a ^ "," ^ aux b

  let of_string = function
    | "N"  -> N
    | "L"  -> L
    | "R"  -> R
    | "LR" -> LR
    | _ -> assert false

end

module Term = struct

  type t = Var of string | Const of Dom.t 

  let unvar = function
    | Var x -> x
    | Const _ -> raise (Invalid_argument "unvar is undefined for Consts")

  let unconst = function
    | Var _ -> raise (Invalid_argument "unconst is undefined for Vars")
    | Const c -> c

  let rec fv_list = function
    | [] -> []
    | Const _ :: trms -> fv_list trms
    | Var x :: trms -> x :: fv_list trms

  let equal t t' = match t, t' with
    | Var x, Var x' -> String.equal x x'
    | Const d, Const d' -> Dom.equal d d'
    | _ -> false

  let to_string = function
    | Var x -> Printf.sprintf "Var %s" x
    | Const d -> Printf.sprintf "Const %s" (Dom.to_string d)

  let value_to_string = function
    | Var x -> Printf.sprintf "%s" x
    | Const d -> Printf.sprintf "%s" (Dom.to_string d)

  let rec list_to_string trms =
    match trms with
    | [] -> ""
    | (Var x) :: trms -> if List.is_empty trms then x
                         else Printf.sprintf "%s, %s" x (list_to_string trms)
    | (Const d) :: trms -> if List.is_empty trms then (Dom.to_string d)
                           else Printf.sprintf "%s, %s" (Dom.to_string d) (list_to_string trms)

end


type ty =
  | Cau
  | Sup

let ty_to_string = function
  | Cau -> "causable"
  | Sup -> "suppressable"

type t =
  | TT
  | FF
  | EqConst of string * Dom.t
  | Predicate of string * Term.t list
  | Neg of t
  | And of Side.t * (t list)
  | Or of Side.t * (t list)
  | Imp of Side.t * t * t
  | Iff of Side.t * Side.t * t * t
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
  | Type of t * ty

let tt = TT
let ff = FF
let eqconst x d = EqConst (x, d)
let predicate p_name trms = Predicate (p_name, trms)
let neg f = Neg f
let conj s f g = And (s, [f; g])
let disj s f g = Or (s, [f; g])
let conj' s fs = And (s, fs)
let disj' s fs = Or (s, fs)
let imp s f g = Imp (s, f, g)
let iff s t f g = Iff (s, t, f, g)
let exists x f = Exists (x, f)
let forall x f = Forall (x, f)
let prev i f = Prev (i, f)
let next i f = Next (i, f)
let once i f = Once (i, f)
let eventually i f = Eventually (i, f)
let historically i f = Historically (i, f)
let always i f = Always (i, f)
let since s i f g = Since (s, i, f, g)
let until s i f g = Until (s, i, f, g)
let type_ s t = Type (s, t)

(* Rewriting of non-native operators *)
let trigger s i f g = Neg (Since (s, i, Neg f, Neg g))
let release s i f g = Neg (Until (s, i, Neg f, Neg g))

let bigconj = function
  | [] -> tt
  | h::t -> List.fold_left t ~init:h ~f:(conj N)

let bigforall vars f =
  List.fold_right vars ~init:f ~f:forall

let rec fv = function
  | TT | FF -> Set.empty (module String)
  | EqConst (x, _) -> Set.of_list (module String) [x]
  | Predicate (_, trms) -> Set.of_list (module String) (Term.fv_list trms)
  | Exists (x, f)
    | Forall (x, f) -> Set.filter (fv f) ~f:(fun y -> not (String.equal x y))
  | Neg f
    | Prev (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Eventually (_, f)
    | Always (_, f)
    | Next (_, f)
    | Type (f, _) -> fv f
    | Imp (_, f1, f2)
    | Iff (_, _, f1, f2)
    | Since (_, _, f1, f2)
    | Until (_, _, f1, f2) -> Set.union (fv f1) (fv f2)
  | And (_, fs)
    | Or (_, fs) ->
     let f x g = Set.union x (fv g) in
     List.fold_left fs ~init:(Set.empty (module String)) ~f

let rec deg = function
  | TT
    | FF
    | EqConst _ 
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
    | Type (f, _) -> deg f
    | Imp (_, f, g)
    | Iff (_, _, f, g)
    | Since (_, _, f, g)
    | Until (_, _, f, g) -> max 2 (max (deg f) (deg g))
    | And (_, fs)
    | Or (_, fs) -> List.fold_left (List.map fs ~f:deg) ~init:1 ~f:max

let rec collect_predicates l = function
  | TT
    | FF
    | EqConst _ -> l
  | Predicate (r, trms) -> (r, trms) :: l
  | Neg f 
    | Exists (_, f)
    | Forall (_, f)
    | Prev (_, f)
    | Next (_, f)
    | Once (_, f)
    | Eventually (_, f)
    | Historically (_, f)
    | Always(_, f) -> collect_predicates l f
    | Imp (_, f, g)
    | Iff (_, _, f, g)
    | Since (_, _, f, g)
    | Until (_, _, f, g) -> collect_predicates (collect_predicates l f) g
  | Type (f, _) -> collect_predicates l f
  | And (_, fs)
    | Or (_, fs) -> List.fold_left fs ~init:l ~f:collect_predicates

let rec flatten_assoc f = match f with
  | TT | FF | EqConst _ | Predicate _ -> f
  | Neg f -> Neg (flatten_assoc f)
  | Exists (x, f) -> Exists (x, flatten_assoc f)
  | Forall (x, f) -> Forall (x, flatten_assoc f)
  | Prev (i, f) -> Prev (i, flatten_assoc f)
  | Next (i, f) -> Next (i, flatten_assoc f)
  | Once (i, f) -> Once (i, flatten_assoc f)
  | Eventually (i, f) -> Once (i, flatten_assoc f)
  | Historically (i, f) -> Historically (i, flatten_assoc f)
  | Always(i, f) -> Always (i, flatten_assoc f)
  | Imp (s, f, g) -> Imp (s, flatten_assoc f, flatten_assoc g)
  | Iff (s, t, f, g) -> Iff (s, t, flatten_assoc f, flatten_assoc g)
  | Since (s, i, f, g) -> Since (s, i, flatten_assoc f, flatten_assoc g)
  | Until (s, i, f, g) -> Until (s, i, flatten_assoc f, flatten_assoc g)
  | Type (f, ty) -> Type (flatten_assoc f, ty)
  | And (s, fs) when Side.equal s L || Side.equal s N ->
     And (s, List.concat (List.map fs ~f:(fun f -> match f with And (_, fs) -> fs | _ -> [f])))
  | And (s, fs) -> And (s, List.map fs ~f:flatten_assoc)
  | Or (s, fs) when Side.equal s L || Side.equal s N ->
     Or (s, List.concat (List.map fs ~f:(fun f -> match f with Or (_, fs) -> fs | _ -> [f])))
  | Or (s, fs) -> Or (s, List.map fs ~f:flatten_assoc)

let rec to_string_rec l = function
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | EqConst (x, c) -> Printf.sprintf "%s = %s" x (Dom.to_string c)
  | Predicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | Neg f -> Printf.sprintf "¬%a" (fun _ -> to_string_rec 5) f
  | And (s, fs) ->
     let sep = "∧" ^ Side.to_string s in
     let strings = List.map fs ~f:(to_string_rec 4) in
     Util.paren_string l 4 (String.concat ~sep strings)
  | Or (s, fs) ->
     let sep = "∨" ^ Side.to_string s in
     let strings = List.map fs ~f:(to_string_rec 4) in
     Util.paren_string l 3 (String.concat ~sep strings)
  | Imp (s, f, g) -> Printf.sprintf (Util.paren l 5 "%a →%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | Iff (s, t, f, g) -> Printf.sprintf (Util.paren l 5 "%a ↔%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string2) (s, t) (fun _ -> to_string_rec 5) g
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
                            (fun _ -> ty_to_string) t
let to_string = to_string_rec 0
