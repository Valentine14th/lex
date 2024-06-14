open Base

type op = ASum | AAvg | AMed | ACnt | AMin | AMax [@@deriving compare, sexp_of, hash, equal]

let op_to_string = function
  | ASum -> "SUM"
  | AAvg -> "AVG"
  | AMed -> "MED"
  | ACnt -> "CNT"
  | AMin -> "MIN"
  | AMax -> "MAX"

let ret_tt op tt =
  match op, tt with
  | ASum, Dom.TInt   -> Some Dom.TInt
  | ASum, Dom.TFloat -> Some Dom.TFloat
  | AAvg, Dom.TInt   -> Some Dom.TInt
  | AAvg, Dom.TFloat -> Some Dom.TFloat
  | AMed, Dom.TInt   -> Some Dom.TInt
  | AMed, Dom.TFloat -> Some Dom.TFloat
  | ACnt, _          -> Some Dom.TInt
  | AMin, Dom.TInt   -> Some Dom.TInt
  | AMin, Dom.TFloat -> Some Dom.TFloat
  | AMax, Dom.TInt   -> Some Dom.TInt
  | AMax, Dom.TFloat -> Some Dom.TFloat
  | _                -> None

let ret_tt_exn op tt =
  Option.value_exn (ret_tt op tt)

