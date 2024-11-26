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
  | Non, Non
    | Cau, Cau
    | Obs, Obs
    | Sup, Sup
    | CauObs, CauObs
    | CauSup, CauSup
    | Itl, Itl -> true
  | _, _ -> false

let meet a b = match a, b with
  | _, _ when equal a b -> a
  | Non, _      | _, Non      -> Non
  | Cau, Obs    | Obs, Cau    -> Non
  | Cau, Sup    | Sup, Cau    -> Non
  | Cau, _      | _, Cau      -> Cau
  | Obs, _      | _, Obs      -> Obs
  | Sup, CauObs | CauObs, Sup -> Obs
  | Sup, _      | _, Sup      -> Sup
  | CauObs, _   | _, CauObs   -> CauObs
  | CauSup, _   | _, CauSup   -> CauSup
  | Itl, _ -> b (* already covered by equal clause, but LSP doesn't understand *)

let join a b = match a, b with
  | _, _ when equal a b -> a
  | Itl, _      | _, Itl      -> Itl (* Does this make sense? *)
  | CauSup, _   | _, CauSup   -> CauSup
  | CauObs, Sup | Sup, CauObs -> CauSup
  | Cau, Sup    | Sup, Cau    -> CauSup
  | Cau, Obs    | Obs, Cau    -> CauObs
  | Sup, _      | _, Sup      -> Sup
  | CauObs, _   | _, CauObs   -> CauObs
  | Obs, _      | _, Obs      -> Obs
  | Cau, _      | _, Cau      -> Cau
  | Non, _ -> b (* already covered by equal clause, but LSP doesn't understand *)

let leq a b = equal (join a b) a
let geq a b = equal (meet a b) b

let specialize a b = if leq b a then Some b else None
