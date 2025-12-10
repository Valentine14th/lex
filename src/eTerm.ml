open Core

module Bop = struct

  type t =
    | BAdd | BSub | BMul | BDiv | BPow
    | BFAdd | BFSub | BFMul | BFDiv | BFPow
    | BAnd | BOr | BXor
    | BEq | BNeq | BLt | BLeq | BGt | BGeq
    | BConc [@@deriving compare, sexp_of, hash, equal]

  let to_string = function
    | BAdd -> "+"
    | BSub -> "-"
    | BMul -> "*"
    | BDiv -> "/"
    | BPow -> "**"
    | BFAdd -> "+."
    | BFSub -> "-."
    | BFMul -> "*."
    | BFDiv -> "/."
    | BFPow -> "**."
    | BAnd -> "and"
    | BOr  -> "or"
    | BXor -> "xor"
    | BEq  -> "="
    | BNeq -> "<>"
    | BLt  -> "<"
    | BLeq -> "<="
    | BGt  -> ">"
    | BGeq -> ">="
    | BConc -> "^"

  let to_latex = function
    | BAdd -> "+"
    | BSub -> "-"
    | BMul -> "\\cdot"
    | BDiv -> "/"
    | BPow -> "\\mathsf{pow}"
    | BFAdd -> "+"
    | BFSub -> "-"
    | BFMul -> "\\cdot"
    | BFDiv -> "/"
    | BFPow -> "\\mathsf{pow}"
    | BAnd -> "\\mathtt{AND}"
    | BOr  -> "\\mathtt{OR}"
    | BXor -> "\\mathtt{XOR}"
    | BEq  -> "="
    | BNeq -> "\\neq"
    | BLt  -> "<"
    | BLeq -> "\\leq"
    | BGt  -> ">"
    | BGeq -> "\\geq"
    | BConc -> "\\cdot"

  let prio = function
    | BXor | BOr -> 1
    | BAnd -> 2
    | BEq | BNeq | BLt | BLeq | BGt | BGeq -> 3
    | BAdd | BSub | BFAdd | BFSub | BConc -> 4
    | BMul | BDiv | BFMul | BFDiv -> 5
    | BPow | BFPow -> 6

  let of_bop o typ =
    match o, typ with
    | Term.Bop.BAdd, TypeTerm.TConst Dom.TInt -> BAdd
    | BAdd, TypeTerm.TConst Dom.TFloat -> BFAdd
    | BAdd, TypeTerm.TConst Dom.TStr -> BConc
    | BSub, TypeTerm.TConst Dom.TInt -> BSub
    | BSub, TypeTerm.TConst Dom.TFloat -> BFSub
    | BMul, TypeTerm.TConst Dom.TInt -> BMul
    | BMul, TypeTerm.TConst Dom.TFloat -> BFMul
    | BDiv, TypeTerm.TConst Dom.TInt -> BDiv
    | BDiv, TypeTerm.TConst Dom.TFloat -> BFDiv
    | BPow, TypeTerm.TConst Dom.TInt -> BPow
    | BPow, TypeTerm.TConst Dom.TFloat -> BFPow
    | BAnd, TypeTerm.TConst Dom.TBool -> BAnd
    | BOr,  TypeTerm.TConst Dom.TBool -> BOr
    | BXor, TypeTerm.TConst Dom.TBool -> BXor
    | BEq, _ -> BEq
    | BNeq, _ -> BNeq
    | BLt, _ -> BLt
    | BLeq, _ -> BLeq
    | BGt, _ -> BGt
    | BGeq, _ -> BGeq
    | _ -> assert false

end

include MFOTL_lib.Term.Make(Term.StringVar)(Dom)(Term.Uop)(Bop)(TTerm.PosTypeInfo)

let to_term_bop = function
  | Bop.BAdd | BFAdd -> Term.Bop.BAdd
  | BSub | BFSub -> BSub
  | BConc -> BConc
  | BMul | BFMul -> BMul
  | BDiv | BFDiv -> BDiv
  | BPow | BFPow -> BPow
  | BAnd -> BAnd
  | BOr -> BOr
  | BXor -> BXor
  | BEq -> BEq
  | BNeq -> BNeq
  | BLt -> BLt
  | BLeq -> BLeq
  | BGt -> BGt
  | BGeq -> BGeq

let rec to_term_core = function
  | Var v -> Term.Var v
  | Const c -> Const c
  | App (s, ts) -> App (s, List.map ~f:to_term ts)
  | Unop (o, t) -> Unop (o, to_term t)
  | Binop (t, o, t') -> Binop (to_term t, to_term_bop o, to_term t')
  | Proj (t, p) -> Proj (to_term t, p)
  | Record kvs -> Record (List.map ~f:(fun (k, v) -> (k, to_term v)) kvs)

and to_term t = { trm = to_term_core t.trm; info = Term.{ pos = t.info.pos } }

let rec of_tterm_core typ = function
  | TTerm.Var v -> Var v
  | Const c -> Const c
  | App (s, ts) -> App (s, List.map ~f:of_tterm ts)
  | Unop (o, t) -> Unop (o, of_tterm t)
  | Binop (t, o, t') -> Binop (of_tterm t, Bop.of_bop o typ, of_tterm t')
  | Proj (t, p) -> Proj (of_tterm t, p)
  | Record kvs -> Record (List.map ~f:(fun (k, v) -> (k, of_tterm v)) kvs)

and of_tterm t = { trm = of_tterm_core t.info.typ t.trm; info = t.info }

let of_tterms = List.map ~f:of_tterm
