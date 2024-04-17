open Core
open Lex

type tstmt =
  | TSImport  of string list * bool
  | TSSection  of section_kind * string * string
  | TSRule    of string list * rule * rule_type * rule_constr list * string option
  | TSEvent   of ident * (Lexing.position * ident * ident) list * pol * string option
  | TSType    of ident * typ

type tevent = (Lexing.position * ident * ident) list * pol * string option

type var_map = (ident, (ident * typ), Base.String.comparator_witness) Map.t

type tprog =
  {
    tstmts: tstmt list;
    taliases: (ident, typ, Base.String.comparator_witness) Map.t; (* maps type aliases to their underlying type *)
    tevents: (ident, tevent, Base.String.comparator_witness) Map.t; (* maps event names to their definitions *)
    variables: (ident, var_map, Base.String.comparator_witness) Map.t; (* maps section labels to variables used in section *)
    exceptions: (string, Formula.t list, Base.String.comparator_witness) Map.t
  }

let tempty =
  {
    tstmts = [];
    taliases = Map.empty (module String);
    tevents = Map.empty (module String);
    variables = Map.empty (module String); 
    exceptions = Map.empty (module String)
  }

let add_tstmt tstmt tprog = { tprog with tstmts = tstmt::tprog.tstmts }

let add_talias name typ tprog pos =
  (* TODO: allow for overwriting/reusing existing type names *)
  let aliases =
    try Map.add_exn tprog.taliases ~key:name ~data:typ 
    with _ -> Util.type_error (Printf.sprintf "type alias %s already exists" name) pos
  in
  { tprog with taliases = aliases; tstmts = TSType (name, typ)::tprog.tstmts }

let add_tevent name args pol ds tprog pos =
  let event = (args, pol, ds) in
  (* TODO: allow for overwriting/reusing event names *)
  let events =
    try Map.add_exn tprog.tevents ~key:name ~data:event
    with _ -> Util.type_error (Printf.sprintf "event %s already exists" name) pos
  in
  { tprog with tevents = events; tstmts = TSEvent (name, args, pol, ds)::tprog.tstmts}

let add_vars vs names tprog pos =
  let variables =
    try List.fold_left ~init:tprog.variables ~f:(fun v_map name -> Map.add_exn v_map ~key:name ~data:vs) names
    with _ -> Util.label_error ("one of the labels: [" ^ String.concat ~sep:", " names ^ "] has already been defined. (rules must be uniquely identifiable)") pos
  in
  { tprog with variables = variables }

let is_trule = function
  | TSRule _ -> true
  | _ -> false

let string_of_tstmt ?(i=0) =
  function
  | TSImport (idents, star) ->
     Printf.sprintf "import %s%s"
       (String.concat ~sep:"." idents)
       (if star then ".*" else "")
  | TSSection (section_kind, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Etc.tabs i)
       (string_of_section_kind section_kind)
       label
       (if String.equal title "" then "" else Printf.sprintf ": \"%s\"" title)
  | TSRule (labels, rule, rule_type, rule_constrs, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string s i
          | None -> ""
      in
     Printf.sprintf "%srule%s\n%s\n%s%s%s%s"
       (Etc.tabs i)
       (String.concat ~sep:" " labels)
       (string_of_rule (i+1) rule)
       (Etc.tabs i)
       (string_of_rule_type rule_type)
       (if List.is_empty rule_constrs then
          ""
        else
          Etc.tabs i ^ (string_of_rule_constrs rule_constrs))
       description
  | TSEvent (name, typed_args, pol, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
      Printf.sprintf "%s%s event %s\n%s%s"
          (Etc.tabs i)
          (string_of_pol pol)
          name
          description
          (string_of_args typed_args i)
  | TSType (name, typ) -> "type " ^ name ^ " is " ^ (string_of_typ typ)

let string_of_signature signature =
  match signature with
  | name, typed_idents ->
     Printf.sprintf "%s(%s)"
       name
       (String.concat ~sep:", " (List.map typed_idents ~f:string_of_typed_idents))
    
let string_of_tprog tprog =
  (* String.concat ~sep:"\n\n" (List.map prog.stmts ~f:string_of_stmt) *)
  String.concat ~sep:"\n" (List.map tprog.tstmts ~f:string_of_tstmt)
