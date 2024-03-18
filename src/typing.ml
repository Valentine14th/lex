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

let add_exception f ident s =
  { s with exceptions = Map.add_multi s.exceptions ~key:ident ~data:f }

let set_labels section_kind label s =
  { s with labels = Labels.set section_kind label s.labels }

let collect_labels s =
  Labels.collect s.labels

let c = ref 0
let fresh () = incr c; string_of_int !c

let type_rule s = function
  | SRule (label, rule, rule_type, rule_constrs) -> begin
      let label0 = Option.value_map label ~default:(fresh ()) ~f:(fun x -> x) in
      let labels = label0 :: (collect_labels s) in
      let s, rule = 
        match rule with
        | Exception (f, ident) ->
           let p_name = "Exception" ^ label0 in
           let vars = Set.elements (Set.union_list (module String) (List.map f ~f:Formula.fv)) in
           let terms = List.map vars ~f:(fun x -> Formula.Term.Var x) in
           let pred = Formula.predicate p_name terms in
           add_exception pred ident s, Constitutive (f, [pred])
        | _ ->
           s, rule
      in
      add_tstmt (TSRule (labels, rule, rule_type, rule_constrs)) s
    end  
  | _ -> assert false

let type_stmt s = function
  | SImport (idents, star) -> add_tstmt (TSImport (idents, star)) s
  | SSection (section_kind, label, _) -> set_labels section_kind label s
  | SEvent _ -> s
  | SRule _ as rule -> type_rule s rule

let do_type tprog =
  let s = List.fold_left tprog.stmts ~init:empty ~f:type_stmt in
  {
    tstmts = List.rev s.tprog.tstmts;
    exceptions = s.exceptions
  }

