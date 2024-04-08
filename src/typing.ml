open Core

open Lex
open Tlex

module Labels = struct

  type t =
    {
      law: ident option;
      title: ident option;
      chapter: ident option;
      section: ident option;
      article: ident option;
      paragraph: ident option;
      point: ident option;
      subpoint: ident option
    }

  let empty =
    {
      law = None;
      title = None;
      chapter = None;
      section = None;
      article = None;
      paragraph = None;
      point = None;
      subpoint = None
    }

  let set section_kind label l =
    match section_kind with
    | Law       -> { empty with law       = Some label }
    | Title     -> { l     with title     = Some label; subpoint = None; point = None; paragraph = None; article = None; section = None; chapter = None }
    | Chapter   -> { l     with chapter   = Some label; subpoint = None; point = None; paragraph = None; article = None; section = None }
    | Section   -> { l     with section   = Some label; subpoint = None; point = None; paragraph = None; article = None}
    | Article   -> { l     with article   = Some label; subpoint = None; point = None; paragraph = None }
    | Paragraph -> { l     with paragraph = Some label; subpoint = None; point = None }
    | Point     -> { l     with point     = Some label; subpoint = None}
    | Subpoint  -> { l     with subpoint  = Some label }

  let collect l =
    let ls = [
      l.law;
      l.title;
      l.chapter;
      l.section;
      l.article;
      l.paragraph;
      l.point;
      l.subpoint
    ] in
    List.filter_map ls ~f:(fun x -> x)

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

let add_talias alias typ s pos =
  { s with tprog = Tlex.add_talias alias typ s.tprog pos }

let add_tevent name args pol ds s pos =
  { s with tprog = Tlex.add_tevent name args pol ds s.tprog pos }

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

(* TODO: forward the error further up in the compilation process
         such that it can be reported together with file name,
         and location in file *)

let string_of_const = function
  | Dom.Int i -> string_of_int i
  | Dom.Str s -> s
  | Dom.Float f -> string_of_float f

let typ_of_const = function
  | Dom.Int _ -> TInt
  | Dom.Str _ -> TString
  | Dom.Float _ -> assert false (* floats are not supported yet *)

(* TODO: currently the error location `pos` is the beginning of the rul
         it might be helpful to have pointers inside the rule,
         e.g. to the predicate name, or variable names
         this would require changes to formaula.ml *)
let type_formulas fs s pos =
  let predicates = List.fold_left (List.map fs ~f:(fun f -> Formula.collect_predicates [] f)) ~init:[] ~f:(fun l ps -> List.concat [l; ps]) in
  let type_var (_, v, t_alias) typed_vars =
    let t = match Map.find s.tprog.taliases t_alias with
      | Some typ -> typ
      | None -> Util.type_error ("Type alias " ^ t_alias ^ " is undefined") pos
    in
    match v with
    | Formula.Term.Var x -> begin match Map.find typed_vars x with
      | Some (a', t') ->
        begin match (compare_aliases (t_alias, t) (a', t')) with
          | true -> typed_vars
          | false -> Util.type_error ("Variable " ^ x ^ " has type \"" ^ a' ^ ":" ^ (string_of_typ t') ^ "\" but was expected to have type \"" ^ t_alias ^ ":" ^ (string_of_typ t)) pos
        end
      | None -> Map.add_exn typed_vars ~key:x ~data:(t_alias, t)
      end
    | Const c ->
      begin match type_check_constant c t with
        | true -> typed_vars
        | false -> Util.type_error ("Constant " ^ (string_of_const c) ^ " has type \"" ^ (string_of_typ (typ_of_const c)) ^ "\" but expected \"" ^ (string_of_typ t)) pos
    end
  in
  let type_vars event_name vars t_vars =
    let t_vars' =
      match Map.find s.tprog.tevents event_name with
        | Some (args, _, _) ->
          List.fold2 args vars ~init:t_vars ~f:(fun t_vars (pos, _, type_alias) v -> type_var (pos, v, type_alias) t_vars) (* list of triples with (variable name, type alias (according to position as argument), actual type of alias)*)
        | None -> Util.type_error ("Event \"" ^ event_name ^ "\" is undefined") pos
      in
      match t_vars' with
        | Ok t_vars'' -> t_vars''
        | Unequal_lengths -> Util.type_error ("Number of arguments doesn't match for event \"" ^ event_name ^ "\"") pos
  in
  List.fold_left predicates ~init:(Map.empty (module String)) ~f:(fun t_vars (n, ts) -> type_vars n ts t_vars)
  |> ignore

let type_rule s pos = function
  | SRule (_, label, rule, rule_type, rule_constrs) -> begin
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
      type_formulas fs s pos;
      add_tstmt (TSRule (labels, rule, rule_type, rule_constrs)) s
    end  
  | _ -> assert false

let type_stmt s = function
  | SImport (_, idents, star) -> add_tstmt (TSImport (idents, star)) s
  | SSection (_, section_kind, label, _) -> set_labels section_kind label s
  | SRule (pos, _, _, _, _) as rule -> type_rule s pos rule
  | SEvent (pos, name, args, pol, ds) -> add_tevent name args pol ds s pos
  | SType (pos, name, typ) -> add_talias name typ s pos

let do_type tprog =
  let s = List.fold_left tprog.stmts ~init:empty ~f:type_stmt in
  {
    tstmts = List.rev s.tprog.tstmts;
    taliases = s.tprog.taliases;
    tevents = s.tprog.tevents;
    rule_variables = s.tprog.rule_variables;
    exceptions = s.exceptions
  }

