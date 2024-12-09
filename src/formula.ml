open Core
open Sformula

module Modules = MFOTL_lib.Modules
module Side = MFOTL_lib.Side

type info_type = {
    variable_instantiations: (string * Term.t) list;
    pos: LexingInfo.t
  } [@@deriving compare, sexp_of, hash, equal]

let info_of_pos pos = { pos; variable_instantiations = [] }

module Info : Modules.I with type t = info_type = struct
  
  type t = info_type [@@deriving compare, sexp_of, hash, equal]

  let rec string_of_instantiations = function
    | [] -> ""
    | [(x, t)] -> Printf.sprintf "%s <- %s" x (Term.value_to_string t)
    | (x, t) :: insts ->  Printf.sprintf "%s <- %s; %s" x (Term.value_to_string t) (string_of_instantiations insts)

  let to_string _ s info =
    match info.variable_instantiations with
    | [] -> s
    | _ -> Printf.sprintf "(%s; %s)" s (string_of_instantiations info.variable_instantiations)

  let dummy = { variable_instantiations = []; pos = LexingInfo.dummy }

end

module StringVar = Term.StringVar

include MFOTL_lib.MFOTL.Make(Info)(StringVar)(Dom)(Term)

let rec init (sf: Sformula.t) : t =
  let info = info_of_pos sf.pos in
  let form = 
    match sf.f with
    | SConst (Dom.Bool true) -> tt
    | SConst (Dom.Bool false) -> ff
    | SApp (s, sfs) -> predicate s (List.map sfs ~f:Term.init)
    | SAgg (s, op, x, y, f) -> agg s op (Term.init x) y (init f)
    | SBop (None, f, op, g) when Sformula.Bop.is_relational op ->
       begin
         let binop = match op with
           | Sformula.Bop.BEq -> Term.Bop.BEq
           | BNeq -> BNeq
           | BLt -> BLt
           | BLeq -> BLeq
           | BGt -> BGt
           | BGeq -> BGeq
           | _ -> assert false in
         term (Term.make (Term.Binop (Term.init f, binop, Term.init g)) { pos = sf.pos })
       end
    | SBop (s_opt, f, op, g) ->
       begin
         match op with
         | Sformula.Bop.BAnd -> conj (Side.value s_opt) (init f) (init g)
         | BOr -> disj (Side.value s_opt) (init f) (init g)
         | BImp -> imp (Side.value s_opt) (init f) (init g)
         | _ -> assert false
       end
    | SBop2 (s2_opt, f, op, g) ->
       begin
         match op with
         | Sformula.Bop2.BIff -> let s1, s2 = Side.value2 s2_opt in
                                 iff s1 s2 (init f) (init g) info info
       end
    | SUop (op, f) ->
       begin
         match op with
         | Sformula.Uop.UNot -> neg (init f)
         | _ -> assert false
       end
    | SExists (xs, f) -> (List.fold_right xs ~init:(init f)
                            ~f:(fun x f -> make (exists x f) info)).form
    | SForall (xs, f) -> (List.fold_right xs ~init:(init f)
                            ~f:(fun x f -> make (forall x f) info)).form
    | SBtop (s_opt, i, f, btop, g) ->
       begin
         match btop with
         | Sformula.Btop.BSince -> since (Side.value s_opt) i (init f) (init g)
         | BUntil -> until (Side.value s_opt) i (init f) (init g)
         | BRelease -> release (Side.value s_opt) i (init f) (init g) info info info 
         | BTrigger -> trigger (Side.value s_opt) i (init f) (init g) info info info 
       end
    | SUtop (i, utop, f) ->
       begin
         match utop with
         | Sformula.Utop.UNext -> next i (init f)
         | UPrev -> prev i (init f)
         | UAlways -> always i (init f)
         | UHistorically -> historically i (init f)
         | UEventually -> eventually i (init f)
         | UOnce -> once i (init f)
       end
    | _ -> assert false
  in make form info
