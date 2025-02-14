open Core

module Modules = MFOTL_lib.Modules

type pos_info_type = {
    pos: LexingInfo.t;
  } [@@deriving compare, sexp_of, hash, equal]

module PosInfo : Modules.I with type t = pos_info_type = struct

  type t = pos_info_type [@@deriving compare, sexp_of, hash, equal]

  let to_string _ s _ = s
  let dummy = { pos = LexingInfo.dummy }

end

module StringVar : Modules.V with type t = string and type comparator_witness = String.comparator_witness = struct

  module T = struct

    type t = string [@@deriving compare, sexp_of, hash, equal]
    
    let to_string s = s
    let to_latex s = Printf.sprintf "\\mathit{%s}" s
    let ident s = s
    let of_ident s = s

    let replace _ z = z
    let equal_ident = equal
    
  end

  include T
  
  let comparator = String.comparator
  type comparator_witness = String.comparator_witness
  
end

module Uop = struct

  type t =
    | USub
    | UNot [@@deriving compare, sexp_of, hash, equal]

  let to_string = function
    | USub -> "-"
    | UNot -> "!"

  let to_latex = function
    | USub -> "-"
    | UNot -> "\\neg"

  let prio _ = 10

end

module Bop = struct

  type t =
    | BAdd | BSub | BMul | BDiv | BPow
    | BAnd | BOr | BXor
    | BEq | BNeq | BLt | BLeq | BGt | BGeq  [@@deriving compare, sexp_of, hash, equal]

  let to_string = function
    | BAdd -> "+"
    | BSub -> "-"
    | BMul -> "*"
    | BDiv -> "/"
    | BPow -> "^"
    | BAnd -> "and"
    | BOr  -> "or"
    | BXor -> "xor"
    | BEq  -> "="
    | BNeq -> "<>"
    | BLt  -> "<"
    | BLeq -> "<="
    | BGt  -> ">"
    | BGeq -> ">="

  let to_latex = function
    | BAdd -> "+"
    | BSub -> "-"
    | BMul -> "\\cdot"
    | BDiv -> "/"
    | BPow -> "\\mathsf{pow}"
    | BAnd -> "\\mathtt{AND}"
    | BOr  -> "\\mathtt{OR}"
    | BXor -> "\\mathtt{XOR}"
    | BEq  -> "="
    | BNeq -> "\\neq"
    | BLt  -> "<"
    | BLeq -> "\\leq"
    | BGt  -> ">"
    | BGeq -> "\\geq"

  let prio = function
    | BXor | BOr -> 1
    | BAnd -> 2
    | BEq | BNeq | BLt | BLeq | BGt | BGeq -> 3
    | BAdd | BSub -> 4
    | BMul | BDiv -> 5
    | BPow -> 6

end

include MFOTL_lib.Term.Make(StringVar)(Dom)(Uop)(Bop)(PosInfo)

let rec init (sf: Sformula.t) : t = match sf.f with
  | SConst c -> make (Const c) { pos = sf.pos }
  | SVar s -> make (Var s) { pos = sf.pos }
  | SApp (s, sfs) -> make (App (s, (List.map sfs ~f:init))) { pos = sf.pos }
  | SBop (None, f, op, g) ->
     begin
       let bop = match op with
         | Sformula.Bop.BAnd -> Bop.BAnd
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
       make (Binop (init f, bop, init g)) { pos = sf.pos }
     end
  | SUop (op, f) ->
     begin
       let uop = match op with
         | Sformula.Uop.USub -> Uop.USub
         | UNot -> UNot
       in
       make (Unop (uop, init f)) { pos = sf.pos }
     end
  | _ -> assert false
