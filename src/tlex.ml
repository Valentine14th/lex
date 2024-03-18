open Core
open Lex

type tstmt =
  | TSImport of string list * bool
  | TSection of section_kind * string * string
  | TSEvent  of ident * (ident * typ) list * pol
  | TSRule   of string list * rule * rule_type * rule_constr list

type tprog =
  {
    tstmts: tstmt list;
    exceptions: (string, Formula.t list, Base.String.comparator_witness) Map.t
  }

let tempty =
  {
    tstmts = [];
    exceptions = Map.empty (module String)
  }

let add_tstmt tstmt tprog = { tprog with tstmts = tstmt::tprog.tstmts }

let is_trule = function
  | TSRule _ -> true
  | _ -> false
