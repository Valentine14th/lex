open Core

module Modules = MFOTL_lib.Modules

type tpos_info_type = {
    pos : LexingInfo.t;
    typ : TypeTerm.t;
  } [@@deriving compare, sexp_of, hash, equal]


module PosTypeInfo : Modules.I with type t = tpos_info_type = struct

  type t = tpos_info_type [@@deriving compare, sexp_of, hash, equal]

  let to_string _ s _ = s
  let dummy = { pos = LexingInfo.dummy; typ = TypeTerm.TypeConst (Dom.TBool) }

end

module StringVar = Term.StringVar

include MFOTL_lib.Term.Make(StringVar)(Dom)(Term.Uop)(Term.Bop)(PosTypeInfo)

let rec to_term_core = function
  | Var v -> Term.Var v
  | Const c -> Const c
  | App (s, ts) -> App (s, List.map ~f:to_term ts)
  | Unop (o, t) -> Unop (o, to_term t)
  | Binop (t, o, t') -> Binop (to_term t, o, to_term t')
  | Proj (t, p) -> Proj (to_term t, p)
  | Record kvs -> Record (List.map ~f:(fun (k, v) -> (k, to_term v)) kvs)

and to_term t = { trm = to_term_core t.trm; info = Term.{ pos = t.info.pos } }



