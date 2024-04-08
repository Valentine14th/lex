open Core
open Lex

type tstmt =
  | TSImport  of string list * bool
  | TSection  of section_kind * string * string
  | TSRule    of string list * rule * rule_type * rule_constr list
  | TSEvent   of ident * (Lexing.position * ident * ident) list * pol * string option
  | TSType    of ident * typ

type tevent = (Lexing.position * ident * ident) list * pol * string option

type tprog =
  {
    tstmts: tstmt list;
    taliases: (ident, typ, Base.String.comparator_witness) Map.t; (* maps type aliases to their underlying type *)
    tevents: (ident, tevent, Base.String.comparator_witness) Map.t; (* maps event names to their definitions *)
    rule_variables: (string, (ident * ident * typ), Base.String.comparator_witness) Map.t; (* maps section labels to variables used in section *)
    exceptions: (string, Formula.t list, Base.String.comparator_witness) Map.t
  }

let tempty =
  {
    tstmts = [];
    taliases = Map.empty (module String);
    tevents = Map.empty (module String);
    rule_variables = Map.empty (module String); 
    exceptions = Map.empty (module String)
  }

let add_tstmt tstmt tprog = { tprog with tstmts = tstmt::tprog.tstmts }

let add_talias name typ tprog pos =
  (* TODO: allow for overwriting/reusing existing type names *)
  let tprog_with_alias =
    try
      { tprog with taliases = Map.add_exn tprog.taliases ~key:name ~data:typ }
    with _ ->
      eprintf "Error at %s: type alias %s already exists\n" (Util.string_of_pos pos) name;
      exit (-1)
  in
  add_tstmt (TSType (name, typ)) tprog_with_alias

let add_tevent name args pol ds tprog pos =
  let event = (args, pol, ds) in
  (* TODO: allow for overwriting/reusing event names *)
  let tprog_with_event = 
    try
      { tprog with tevents = Map.add_exn tprog.tevents ~key:name ~data:event }
    with _ ->
      eprintf "Error at %s: event %s already exists\n" (Util.string_of_pos pos) name;
      exit (-1)
  in
  add_tstmt (TSEvent (name, args, pol, ds)) tprog_with_event

let is_trule = function
  | TSRule _ -> true
  | _ -> false
