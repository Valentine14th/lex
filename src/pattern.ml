open Base

module Modules = MFOTL_lib.Modules
module Interval = MFOTL_lib.Interval
module Zinterval = MFOTL_lib.Zinterval
module Enftype = MFOTL_lib.Enftype
module Term = MFOTL_lib.Term

let debug_pattern = ref false
let debug msg = if !debug_pattern then Errors.debug_print ~f_name:(Some "pattern.ml") msg

module type F = sig

  type t
  val to_string: t -> string

end

module MakeSimple (Formula : F) = struct

  type patt =
    | PPresent
    | PEventually   of Interval.t
    | PAlways       of Interval.t
    | PUntil        of Interval.t * Formula.t
    | POnce         of Interval.t
    | PHistorically of Interval.t
    | PSince        of Interval.t * Formula.t

  type t = { patt: patt; fs: Formula.t list }

  let make patt fs = { patt; fs }

  let patt_to_string = function
    | PPresent        -> ""
    | PEventually i   -> Printf.sprintf " eventually %s"                                      (Interval.to_string i)
    | PAlways i       -> Printf.sprintf " always in the future %s"                            (Interval.to_string i)
    | PUntil (i, f)   -> Printf.sprintf " eventually delaying if %s %s" (Formula.to_string f) (Interval.to_string i)
    | POnce i         -> Printf.sprintf " once %s"                                            (Interval.to_string i)
    | PHistorically i -> Printf.sprintf " always in the past %s"                              (Interval.to_string i)
    | PSince (i, f)   -> Printf.sprintf " always since %s %s"           (Formula.to_string f) (Interval.to_string i)

  let to_string pf =
    Printf.sprintf "{p = %s; fs = [%s]}"
      (patt_to_string pf.patt)
      (String.concat ~sep:", " (List.map pf.fs ~f:Formula.to_string))


end

module Make
 (Info : Modules.I)
 (Var  : Modules.V)
 (Dom  : Modules.D)
 (Term : Term.T with type v = Var.t and type d = Dom.t) = struct

  module Formula = MFOTL_lib.MFOTL.Make(Info)(Var)(Dom)(Term)

  include MakeSimple(Formula)

  let formulas_of_patt = function
    | PPresent
      | PEventually _
      | PAlways _
      | POnce _
      | PHistorically _ -> []
    | PUntil (_, f) 
      | PSince (_, f) -> [f]

  let formulas pf =
    formulas_of_patt pf.patt @ pf.fs

  let predicates patt =
    List.concat_map ~f:Formula.predicates (formulas patt)

  let fv_of_patt = function
    | PPresent
      | PEventually _
      | POnce _
      | PAlways _
      | PHistorically _ -> Set.empty (module Var)
    | PUntil (_, f)
      | PSince (_, f) -> Formula.fv f

  let fv pf = 
    Set.union
      (Set.union_list (module Var) (List.map ~f:Formula.fv pf.fs))
      (fv_of_patt pf.patt)

  let strict ?(itl_strict=Map.empty (module String)) (pf: t) : bool =
    match pf.patt with
    | PPresent -> Formula.stricts ~itl_strict pf.fs
    | PEventually i
      | PAlways i ->
       let i = Zinterval.of_interval i in
       not (Zinterval.has_zero i)
       && Formula.stricts ~itl_strict pf.fs
    | PUntil (i, g) ->
       let i = Zinterval.of_interval i in
       not (Zinterval.has_zero (Zinterval.inv i))
       && Formula.stricts ~itl_strict pf.fs
       && Formula.strict ~itl_strict:itl_strict g
    | POnce _
      | PHistorically _ -> Formula.stricts ~itl_strict pf.fs
    | PSince (_, g) ->
       Formula.stricts ~itl_strict pf.fs
       && Formula.strict ~itl_strict:itl_strict g

  let relative_interval ?(itl_itvs=Map.empty (module String)) (pf: t): Zinterval.t =
    match pf.patt with
    | PPresent -> Formula.relative_intervals ~itl_itvs pf.fs
    | PEventually i
      | PAlways i ->
       let i = Zinterval.of_interval i in
       let j = Formula.relative_intervals ~itl_itvs pf.fs in
       Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
    | PUntil (i, g) ->
       let i = Zinterval.of_interval i in
       let j = Formula.relative_intervals ~itl_itvs pf.fs in
       Zinterval.lub 
         (Zinterval.sum (Zinterval.to_zero i) (Formula.relative_interval ~itl_itvs:itl_itvs g))
         (Zinterval.sum i j)
    | POnce i
      | PHistorically i ->
       let i = Zinterval.of_interval i in
       let j = Formula.relative_intervals ~itl_itvs pf.fs in
       Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i j)
    | PSince (i, g) ->
       let i = Zinterval.of_interval i in
       let j = Formula.relative_intervals ~itl_itvs pf.fs in
       Zinterval.lub
         (Zinterval.sum (Zinterval.to_zero i) j)
         (Zinterval.sum i (Formula.relative_interval ~itl_itvs:itl_itvs g))

  let relative_past ?(itl_itvs=Map.empty (module String)) pf =
    let itv = relative_interval ~itl_itvs pf in
    debug (Printf.sprintf "relative_interval (%s) = %s" (to_string pf) (Zinterval.to_string itv));
    Zinterval.is_nonpositive itv

  let observable (module Sig : Modules.S) ?(itl_observable=Map.empty (module String)) pf =
    List.for_all (predicates pf)
      ~f:(fun (e, _) -> match Map.find itl_observable e with
                        | Some b -> b
                        | None -> Enftype.is_observable (Sig.enftype_of_pred e))

  let strictly_relative_past
        (module Sig : Modules.S)
        ?(itl_itvs=Map.empty (module String))
        ?(itl_strict=Map.empty (module String))
        ?(itl_observable=Map.empty (module String)) pf =
    let is_relative_past = relative_past ~itl_itvs pf in
    let is_strict = strict ~itl_strict pf in
    let is_observable = observable (module Sig) ~itl_observable pf in
    debug (Printf.sprintf "strictly_relative_past (%s)" (to_string pf));
    debug (Printf.sprintf "is_relative_past: %b" is_relative_past);
    debug (Printf.sprintf "is_strict: %b" is_strict);
    debug (Printf.sprintf "is_observable: %b" is_observable);
    is_relative_past && is_strict && is_observable

  let rec solve_past_guarded (module Sig : Modules.S) ?(pg_map=Map.empty (module String)) x p (tpf: t) =
    let open Formula.MFOTL_Enforceability(Sig) in
    let solve_past_guarded_multiple =
      List.concat_map ~f:(solve_past_guarded pg_map x p)
      (*MFOTL_lib.Etc.inter_string_set_list (List.map ~f:(solve_past_guarded pg_map x p) fs)*)
    in
    (* TODO: verify this, implementation follow the implementatoin of is_past_guarded *)
    let r = 
      match tpf.patt with
      | PPresent ->
         solve_past_guarded_multiple tpf.fs
      | POnce _
        | PEventually _ when p ->
         solve_past_guarded_multiple tpf.fs
      (* TODO: is this correct, strictly following the PG rules (and translating (Eventually_I phi) to (true Until_I phi)), x would need to be PG(x)+ in the formula 'true', which would be false *)
      (* this is ipmlemented by following the implementation of is_past_guarded *)
      | PEventually i 
        | POnce i when Interval.has_zero i ->
         solve_past_guarded_multiple tpf.fs
      | PHistorically _ 
        | PAlways _  when not p ->
         solve_past_guarded_multiple tpf.fs
      | PHistorically i when Interval.has_zero i ->
         solve_past_guarded_multiple tpf.fs
      | PAlways _ -> []
      | PSince (i, g) when p ->
         (if not (Interval.has_zero i) then
            solve_past_guarded_multiple tpf.fs
          else
            []) @ solve_past_guarded pg_map x p g
      | PSince (i, g) when Interval.has_zero i ->
         solve_past_guarded pg_map x p g
      | PUntil (i, g) when p ->
         (if not (Interval.has_zero i) then
            solve_past_guarded pg_map x p g
          else
            []) @ solve_past_guarded_multiple (g::tpf.fs)
      | PUntil (i, _) when Interval.has_zero i ->
         solve_past_guarded_multiple tpf.fs
      | _ -> []
    in (*Stdio.print_endline (Printf.sprintf "solve_past_guarded(%s,%s)=%s" (Var.to_string x) (to_string tpf) (MFOTL_lib.Etc.string_set_list_to_string r));*)
       r
    
  and solve_past_guarded_multiple (module Sig : Modules.S) ?(pg_map=Map.empty (module String)) x p (tpfs: t list) =
    MFOTL_lib.Etc.inter_string_set_list (List.map ~f:(solve_past_guarded (module Sig) ~pg_map x p) tpfs)
    
  let is_past_guarded (module Sig : Modules.S) ?(pg_map=Map.empty (module String)) x p (tpf: t) =
    not (List.is_empty (solve_past_guarded (module Sig) ~pg_map x p tpf))


end
