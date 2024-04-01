open Core

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
  | And of Side.t * t * t
  | Or of Side.t * t * t
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
let conj s f g = And (s, f, g)
let disj s f g = Or (s, f, g)
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
  | And (_, f1, f2)
    | Or (_, f1, f2)
    | Imp (_, f1, f2)
    | Iff (_, _, f1, f2)
    | Since (_, _, f1, f2)
    | Until (_, _, f1, f2) -> Set.union (fv f1) (fv f2)

let paren h k x = if h>k then "("^^x^^")" else x

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
  | And (_, f, g)
    | Or (_, f, g)
    | Imp (_, f, g)
    | Iff (_, _, f, g)
    | Since (_, _, f, g)
    | Until (_, _, f, g) -> collect_predicates (collect_predicates l f) g
  | Type (f, _) -> collect_predicates l f

let rec to_string_rec l = function
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | EqConst (x, c) -> Printf.sprintf "%s = %s" x (Dom.to_string c)
  | Predicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | Neg f -> Printf.sprintf "¬%a" (fun _ -> to_string_rec 5) f
  | And (s, f, g) -> Printf.sprintf (paren l 4 "%a ∧%a %a") (fun _ -> to_string_rec 4) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 4) g
  | Or (s, f, g) -> Printf.sprintf (paren l 3 "%a ∨%a %a") (fun _ -> to_string_rec 3) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 4) g
  | Imp (s, f, g) -> Printf.sprintf (paren l 5 "%a →%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | Iff (s, t, f, g) -> Printf.sprintf (paren l 5 "%a ↔%a %a") (fun _ -> to_string_rec 5) f (fun _ -> Side.to_string2) (s, t) (fun _ -> to_string_rec 5) g
  | Exists (x, f) -> Printf.sprintf (paren l 5 "∃%s. %a") x (fun _ -> to_string_rec 5) f
  | Forall (x, f) -> Printf.sprintf (paren l 5 "∀%s. %a") x (fun _ -> to_string_rec 5) f
  | Prev (i, f) -> Printf.sprintf (paren l 5 "●%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Next (i, f) -> Printf.sprintf (paren l 5 "○%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Once (i, f) -> Printf.sprintf (paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Eventually (i, f) -> Printf.sprintf (paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Historically (i, f) -> Printf.sprintf (paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Always (i, f) -> Printf.sprintf (paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5) f
  | Since (s, i, f, g) -> Printf.sprintf (paren l 0 "%a S%a%a %a") (fun _ -> to_string_rec 5) f
                          (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | Until (s, i, f, g) -> Printf.sprintf (paren l 0 "%a U%a%a %a") (fun _ -> to_string_rec 5) f
                            (fun _ -> Interval.to_string) i (fun _ -> Side.to_string) s (fun _ -> to_string_rec 5) g
  | Type (f, t) -> Printf.sprintf (paren l 0 "%a : %a") (fun _ -> to_string_rec 5) f
                            (fun _ -> ty_to_string) t
let to_string = to_string_rec 0
