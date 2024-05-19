(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)


(* Unbounded [i,+∞) *)
type ut = UI of int

(* Bounded [i,j] *)
type bt = BI of int * int

type t = B of bt | U of ut

let equal i i' = match i, i' with
  | B (BI (a, b)), B (BI (a', b')) -> Int.equal a a' && Int.equal b b'
  | U (UI a), U (UI a') -> Int.equal a a'
  | _ -> false

let lclosed_UI i = U (UI i)
let lopen_UI i = U (UI (i + 1))

let nonempty_BI l r = if l <= r then BI (l, r) else raise (Invalid_argument "empty interval")
let lopen_ropen_BI i j = B (nonempty_BI (i + 1) (j - 1))
let lopen_rclosed_BI i j = B (nonempty_BI (i + 1) j)
let lclosed_ropen_BI i j = B (nonempty_BI i (j - 1))
let lclosed_rclosed_BI i j = B (nonempty_BI i j)

let singleton i = lclosed_rclosed_BI i i
let is_zero i = i == singleton 0

let full = U (UI 0)

let case f1 f2 = function
  | B i -> f1 i
  | U i -> f2 i

let is_bounded = function
  | B _ -> true
  | U _ -> false

let is_bounded_exn op = function
  | B _ -> ()
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator: %s" op))

let sub i t = match i with
  | B (BI (a, b)) -> B (BI (a, b - t))
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator"))

let sub2 i t = match i with
  | B (BI (a, b)) -> B (BI (max 0 (a - t), max 0 (b - t)))
  | U (UI a) -> U (UI (max 0 (a - t)))

let boundaries = function
  | B (BI (a, b)) -> (a, b)
  | U _ -> raise (Invalid_argument (Printf.sprintf "unbounded future operator"))

let map f1 f2 = case (fun i -> B (f1 i)) (fun i -> U (f2 i))

let mem t =
  let mem_UI t (UI l) = l <= t in
  let mem_BI t (BI (l, r)) = l <= t && t <= r in
  case (mem_BI t) (mem_UI t)

let left =
  let left_UI (UI l) = l in
  let left_BI (BI (l, _)) = l in
  case left_BI left_UI

let right =
  let right_UI (UI _) = None in
  let right_BI (BI (_, r)) = Some(r) in
  case right_BI right_UI

let lub i i' =
  let l = min (left i) (left i') in
  match right i, right i' with
  | Some r, Some r' -> lclosed_rclosed_BI l (max r r')
  | _ -> lclosed_UI l

let below_UI t (UI l) = t < l
let below_BI t (BI (l, _)) = t < l
let below t = case (below_BI t) (below_UI t)

(* Check if t > interval *)
let above_UI _ (UI _) = false
let above_BI t (BI (_, r)) = t > r
let above t = case (above_BI t) (above_UI t)

let to_string_BI = function
  | BI (i, j) -> Printf.sprintf "[%d,%d]" i j

let to_string = function
  | U (UI 0) -> ""
  | U (UI i) -> Printf.sprintf "[%d,∞)" i
  | B i -> Printf.sprintf "%a" (fun _ -> to_string_BI) i

let of_bound = function
  | Interval.C s -> true,  Lextime.Span.to_int s
  | O s          -> false, Lextime.Span.to_int s

let of_interval = function
  | Interval.U b ->
     let closed, i = of_bound b in
     (if closed then lclosed_UI else lopen_UI) i
  | B (lb, rb) ->
     let lclosed, li = of_bound lb
     and rclosed, ri = of_bound rb in
     (match lclosed, rclosed with
      | true, true   -> lclosed_rclosed_BI
      | true, false  -> lclosed_ropen_BI
      | false, true  -> lopen_rclosed_BI
      | false, false -> lopen_ropen_BI) li ri

let to_interval = function
  | B (BI (l, r)) -> Interval.B (C (Lextime.Span.seconds l), C (Lextime.Span.seconds r))
  | U (UI i)      -> U (C (Lextime.Span.seconds i))
