open Core

open Lex
open Tlex

module Labels = struct

  type t =
    {
      chapter: ident option;
      article: ident option;
      paragraph: ident option;
      point: ident option
    }

  let empty =
    {
      chapter = None;
      article = None;
      paragraph = None;
      point = None
    }

  let set section_kind label l =
    match section_kind with
    | Chapter   -> { empty with chapter   = Some label }
    | Article   -> { l     with article   = Some label; paragraph = None; point = None }
    | Paragraph -> { l     with paragraph = Some label; point     = None }
    | Point     -> { l     with point     = Some label }

  let collect l =
    List.filter_map [l.chapter; l.article; l.paragraph; l.point] ~f:(fun x -> x)

end

type t =
  {
    tprog: tprog;
    labels: Labels.t;
    exceptions: (string, Formula.t list, Base.String.comparator_witness) Map.t
  }

let empty =
  {
    tprog = tempty;
    labels = Labels.empty;
    exceptions = Map.empty (module String)
  }

let add_tstmt tstmt s =
  { s with tprog = Tlex.add_tstmt tstmt s.tprog }

let add_talias alias typ s =
  { s with tprog = Tlex.add_talias alias typ s.tprog }

let add_tevent name args pol ds s =
  { s with tprog = Tlex.add_tevent name args pol ds s.tprog }

let add_exception f ident s =
  { s with exceptions = Map.add_multi s.exceptions ~key:ident ~data:f }

let set_labels section_kind label s =
  { s with labels = Labels.set section_kind label s.labels }

let collect_labels s =
  Labels.collect s.labels

let c = ref 0
let fresh () = incr c; string_of_int !c

let compare_aliases (a1, t1) (a2, t2) = (String.compare a1 a2) = 0 && (Lex.compare_typs t1 t2)

let type_check_constant c t = match (c, t) with
  | Dom.Int _, TInt
    | Dom.Str _, TString -> true
  | Dom.Float _, _ -> false (* floats aren't yet supported by "lex"*)
  | _, _ -> false

let type_formulas fs s =
  let predicates = List.fold_left (List.map fs ~f:(fun f -> Formula.collect_predicates [] f)) ~init:[] ~f:(fun l ps -> List.concat [l; ps]) in
  let type_var (v, t_alias) typed_vars =
    let t = match Map.find s.tprog.taliases t_alias with
      | Some typ -> typ
      | None -> assert false (* TODO: add meaningful error message when type alias isn't found *)
    in
    match v with
    | Formula.Term.Var x -> begin match Map.find typed_vars x with
      | Some (a', t') -> assert (compare_aliases (t_alias, t) (a', t')); (* TODO: add meaningful error message when variable typing doesn't match *)
                         typed_vars
      | None -> Map.add_exn typed_vars ~key:x ~data:(t_alias, t)
      end
    | Const c -> assert (type_check_constant c t);
                 typed_vars
  in
  let type_vars event_name vars t_vars =
    let t_vars' =
      match Map.find s.tprog.tevents event_name with
        | Some (args, _, _) ->
          List.fold2 args vars ~init:t_vars ~f:(fun t_vars (_, type_alias) v -> type_var (v, type_alias) t_vars) (* list of triples with (variable name, type alias (according to position as argument), actual type of alias)*)
        | None -> assert false (* TODO: add meaningful error message when predicate/event name isn't found *)
      in
      match t_vars' with
        | Ok t_vars'' -> t_vars''
        | Unequal_lengths -> assert false (* TODO: add meaningful error message when number of arguments doesn't match *)
  in
  List.fold_left predicates ~init:(Map.empty (module String)) ~f:(fun t_vars (n, ts) -> type_vars n ts t_vars)
  |> ignore

let type_rule s = function
  | SRule (label, rule, rule_type, rule_constrs) -> begin
      let label0 = Option.value_map label ~default:(fresh ()) ~f:(fun x -> x) in
      let labels = label0 :: (collect_labels s) in
      let s, rule, fs = 
        match rule with
        | Exception (f, ident) ->
           let p_name = "Exception" ^ label0 in
           let vars = Set.elements (Set.union_list (module String) (List.map f ~f:Formula.fv)) in
           let terms = List.map vars ~f:(fun x -> Formula.Term.Var x) in
           let pred = Formula.predicate p_name terms in
           add_exception pred ident s, Constitutive (f, [pred]), f
        | Obligation (f1, f2)
        | Permission (f1, f2)
        | Constitutive (f1, f2) ->
           s, rule, List.concat [f1; f2]
      in
      type_formulas fs s;
      add_tstmt (TSRule (labels, rule, rule_type, rule_constrs)) s
    end  
  | _ -> assert false

let type_stmt s = function
  | SImport (idents, star) -> add_tstmt (TSImport (idents, star)) s (* TODO: how to type check imports, depends on how imports are actually done in practice *)
  | SSection (section_kind, label, _) -> set_labels section_kind label s
  | SRule _ as rule -> type_rule s rule (* TODO: type check arguments in events of rule *)
  | SEvent (name, args, pol, ds) -> add_tevent name args pol ds s
  | SType (name, typ) -> add_talias name typ s

let do_type tprog =
  let s = List.fold_left tprog.stmts ~init:empty ~f:type_stmt in
  {
    tstmts = List.rev s.tprog.tstmts;
    taliases = s.tprog.taliases;
    tevents = s.tprog.tevents;
    exceptions = s.exceptions
  }

