open Core

type range =
  { start: Lexing.position;
    stop:  Lexing.position }

let compare_range r1 r2 =
  match compare r1.start.pos_cnum r2.start.pos_cnum with
  | 0 -> compare r1.stop.pos_cnum r2.stop.pos_cnum
  | c -> c

let sexp_of_range r =
  let open Sexplib.Sexp in
  List [
    List [Atom "start"; Atom (string_of_int r.start.pos_cnum)];
    List [Atom "stop"; Atom (string_of_int r.stop.pos_cnum)]
  ]

let hash_range r =
  Hashtbl.hash (r.start.pos_cnum, r.stop.pos_cnum)

let hash_fold_range state range =
  let state = Hash.fold_int state range.start.pos_cnum in
  let state = Hash.fold_int state range.start.pos_lnum in
  let state = Hash.fold_int state range.stop.pos_cnum in
  Hash.fold_int state range.stop.pos_lnum

let equal_range r1 r2 =
  r1.start.pos_cnum = r2.start.pos_cnum && r1.stop.pos_cnum = r2.stop.pos_cnum

type t = { ranges: range list } [@@deriving compare, sexp_of, hash, equal]

let cnum (pos : Lexing.position) = pos.pos_cnum - pos.pos_bol + 1

let string_of_position (pos : Lexing.position) =
  Printf.sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (cnum pos)

let string_of_range (r : range) =
  if String.equal r.start.pos_fname r.stop.pos_fname then (
    if Int.equal r.start.pos_lnum r.stop.pos_lnum then (
      if Int.equal (cnum r.start) (cnum r.stop) then
        string_of_position r.start
      else
        Printf.sprintf "%s-%d" (string_of_position r.start) (cnum r.stop)
    )
    else
      Printf.sprintf "%s-%d:%d" (string_of_position r.start) r.stop.pos_lnum (cnum r.stop)
  )
  else
    Printf.sprintf "%s-%s" (string_of_position r.start) (string_of_position r.stop)

let to_string (i : t) =
  String.concat ~sep:", " (List.map ~f:string_of_range i.ranges)
      
let dummy = { ranges = [] }

let create start stop = { ranges = [{ start; stop}] }
let of_loc (start, stop) = { ranges = [{ start; stop}] }
let create1 start = { ranges = [{ start; stop = start }] }

let (<=) (pos : Lexing.position) (pos' : Lexing.position) =
  if String.equal pos.pos_fname pos'.pos_fname then (
    if Int.equal pos.pos_lnum pos'.pos_lnum then
      Int.(cnum pos <= cnum pos')
    else
      Int.(pos.pos_lnum <= pos'.pos_lnum)
  )
  else
    false

let min pos pos' = if pos <= pos' then pos  else pos'
let max pos pos' = if pos <= pos' then pos' else pos

let add_range r r' = { start = min r.start r'.start; stop = max r.stop r'.stop }

let add_range_to_info b (r : range) (i : t) =
  let rec f = function
    | [] -> [r]
    | r'::t ->
      if List.mem t r' ~equal:equal_range then
        t
      else if String.equal r'.start.pos_fname r.start.pos_fname &&
                    (b
                     || Int.equal r.start.pos_lnum r'.stop.pos_lnum && Int.equal (cnum r.start) (cnum r'.stop)
                     || Int.equal r.stop.pos_lnum r'.start.pos_lnum && Int.equal (cnum r.stop) (cnum r'.start)) then
                   (add_range r r') :: t
                else
                  r' :: (f t)
  in { ranges = f i.ranges }

let (++) i i' = List.fold_right i.ranges ~f:(add_range_to_info false) ~init:i'
let (+>) i i' = List.fold_right i.ranges ~f:(add_range_to_info true) ~init:i'

let concr_opt i i'_opt i' =
  match i'_opt with
  | Some i' -> i +> i'
  | None    -> i +> i'

let concl_opt i_opt i i' =
  match i_opt with
  | Some i -> i +> i'
  | None   -> i +> i'

let conclr_opt i_opt i i'_opt i' =
  match i_opt, i'_opt with
  | Some i, Some i' -> i +> i'
  | Some i, None    -> i +> i'
  | None  , Some i' -> i +> i'
  | None  , None    -> i +> i'

let remove_duplicate_ranges i =
  let rec f acc = function
    | [] -> acc
    | r::rs ->
      if List.mem rs r ~equal:equal_range then
        f acc rs 
      else f (r::acc) rs in
  { ranges = f [] i.ranges }

let union_all = function
  | [] -> dummy
  | i::is -> List.fold_left is ~init:i ~f:(++)
                        |> remove_duplicate_ranges
