open Base

module Side = MFOTL_lib.Side
module Interval = MFOTL_lib.Interval
module Enftype = MFOTL_lib.Enftype

module Aop = struct

  type t = MFOTL_lib.Aggregation.op

  let to_string = MFOTL_lib.Aggregation.op_to_string
  
end

module Bop2 = struct

  type t = BIff [@@deriving compare, sexp_of, hash]

  let to_string = function
    | BIff   -> "↔"

  let prio = function
    | BIff   -> 80

end

module Bop = struct

  type t =
    | BAnd | BOr | BImp
    | BAdd | BSub | BMul | BDiv | BPow
    | BEq | BNeq | BLt | BLeq | BGt | BGeq
    [@@deriving compare, sexp_of, hash]

  let is_relational = function
    | BEq | BNeq | BLt | BLeq | BGt | BGeq -> true
    | _ -> false

  let to_string = function
    | BAnd   -> "∧"
    | BOr    -> "∨"
    | BImp   -> "→"
    | BAdd   -> "+"
    | BSub   -> "-"
    | BMul   -> "*"
    | BDiv   -> "/"
    | BPow   -> "**"
    | BEq    -> "="
    | BNeq   -> "≠"
    | BLt    -> "<"
    | BLeq   -> "≤"
    | BGt    -> ">"
    | BGeq   -> "≥"

  let prio = function
    | BPow   -> 10
    | BMul   -> 20
    | BDiv   -> 20
    | BAdd   -> 30
    | BSub   -> 30
    | BEq    -> 40
    | BNeq   -> 40
    | BLt    -> 40
    | BLeq   -> 40
    | BGt    -> 40
    | BGeq   -> 40
    | BAnd   -> 50
    | BOr    -> 60
    | BImp   -> 70

end

module Uop = struct

  type t = USub | UNot
           [@@deriving compare, sexp_of, hash]

  let to_string = function
    | USub  -> "-"
    | UNot  -> "¬"

  let prio = function
    | USub  -> 8
    | UNot  -> 45

end

module Btop = struct

  type t = BSince | BUntil | BRelease | BTrigger
           [@@deriving compare, sexp_of, hash]

  let to_string = function
    | BSince   -> "S"
    | BUntil   -> "U"
    | BRelease -> "R"
    | BTrigger -> "T"

  let prio _ = 49

end

module Utop = struct

  type t = UNext | UPrev | UAlways | UHistorically | UEventually | UOnce
           [@@deriving compare, sexp_of, hash]

  let to_string = function
    | UNext         -> "○"
    | UPrev         -> "●"
    | UAlways       -> "□"
    | UHistorically -> "■"
    | UEventually   -> "◊"
    | UOnce         -> "⧫"

  let prio _ = 47

end

type core_t =
  | SConst of Dom.t
  | SVar of string
  | SApp of string * t list
  | SAgg of string * Aop.t * t * string list * t
  | SBop of Side.t option * t * Bop.t * t
  | SBop2 of (Side.t * Side.t) option * t * Bop2.t * t
  | SUop of Uop.t * t
  | SExists of string list * t
  | SForall of string list * t
  | SBtop of Side.t option * Interval.t * t * Btop.t * t
  | SUtop of Interval.t * Utop.t * t
  | STyp of t * Enftype.t
  | SRecord of (string * t) list
  | SProj of t * string
and t = { f : core_t; pos : LexingInfo.t }

let make pos f = { f; pos }

let const pos c = make pos (SConst c)
let var pos x = make pos (SVar x)
let app pos f es = make pos (SApp (f, es))
let agg pos s op x y e = make pos (SAgg (s, op, x, y, e))
let exists pos xs e = make pos (SExists (xs, e))
let forall pos xs e = make pos (SForall (xs, e))
let bop pos s_opt op l r = make pos (SBop (s_opt, l, op, r))
let bop2 pos s2_opt op l r = make pos (SBop2 (s2_opt, l, op, r))
let uop pos op e = make pos (SUop (op, e))
let btop pos s_opt i op l r = make pos (SBtop (s_opt, i, l, op, r))
let utop pos op i e = make pos (SUtop (i, op, e))
let typ pos e ty = make pos (STyp (e, ty))
let record pos es = make pos (SRecord es)
let proj pos e s = make pos (SProj (e, s))

let rec to_string_rec l = function
  | SConst c -> Dom.to_string c
  | SVar s -> s
  | SApp (f, ts) -> Printf.sprintf "%s(%s)" f (list_to_string ts)
  | SAgg (s, op, x, y, f) -> Printf.sprintf "%s <- %s(%s; %s; %s)"
                               s
                               (Aop.to_string op)
                               (to_string x)
                               (String.concat ~sep:", " y)
                               (to_string_rec 5 f.f)
  | SBop (s_opt, f, bop, g) -> Printf.sprintf "%s %s%s %s"
                                 (to_string_rec (Bop.prio bop) f.f)
                                 (Bop.to_string bop)
                                 (Option.fold s_opt ~init:"" ~f:(fun _ -> Side.to_string))
                                 (to_string_rec (Bop.prio bop) g.f)
  | SBop2 (s2_opt, f, bop, g) -> Printf.sprintf "%s %s%s %s"
                                   (to_string_rec (Bop2.prio bop) f.f)
                                   (Bop2.to_string bop)
                                   (Option.fold s2_opt ~init:"" ~f:(fun _ -> Side.to_string2))
                                   (to_string_rec (Bop2.prio bop) g.f)
  | SUop (uop, f) -> Printf.sprintf "%s %s"
                       (Uop.to_string uop)
                       (to_string_rec (Uop.prio uop) f.f)
  | SExists (xs, f) -> Printf.sprintf (Util.paren l 5 "∃%s. %s")
                         (String.concat ~sep:", " xs)
                         (to_string_rec 5 f.f)
  | SForall (xs, f) -> Printf.sprintf (Util.paren l 5 "∀%s. %s")
                         (String.concat ~sep:", " xs)
                         (to_string_rec 5 f.f)
  | SBtop (s_opt, i, f, btop, g) -> Printf.sprintf "%s %s%s%s %s"
                                      (to_string_rec (Btop.prio btop) f.f)
                                      (Btop.to_string btop)
                                      (Interval.to_string i)
                                      (Option.fold s_opt ~init:"" ~f:(fun _ -> Side.to_string))
                                      (to_string_rec (Btop.prio btop) g.f)
  | SUtop (i, utop, f) -> Printf.sprintf "%s%s %s"
                            (Utop.to_string utop)
                            (Interval.to_string i)
                            (to_string_rec (Utop.prio utop) f.f)
  | STyp (f, ty) -> Printf.sprintf "%s : %s"
                      (to_string_rec 0 f.f)
                      (Enftype.to_string ty)
  | SRecord sfs -> Printf.sprintf "{ %s }"
                    (Util.string_of_string_list
                       (List.map ~f:(fun (s, f) -> Printf.sprintf "%s : %s" s (to_string_rec 0 f.f)) sfs))
  | SProj (f, s) -> Printf.sprintf "%s.%s"
                      (to_string_rec 100 f.f)
                      s

and list_to_string ts = String.concat ~sep:", " (List.map ~f:to_string ts)

and to_string t = to_string_rec 0 t.f
