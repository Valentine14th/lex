open Core
open Lex
open Tlex

type erule =
  | EObligation   of Tformula.t list * Tformula.t list
  | EPermission   of Tformula.t list * Tformula.t list
  | EConstitutive of Tformula.t list * Tformula.t list
  | EException    of Tformula.t list * ident * Tformula.t

type estmt =
  | ESImport  of Lexing.position * string list * import_format
  | ESSection of section_kind * Label.t * string * string tannot option
  | ESRule    of Lexing.position * Label.t * (ident * ident) list * erule * rule_type * rule_constr list * string tannot option
  | ESEvent   of event_type * ident * (Lexing.position * ident * ident) list * pol * string option
  | ESType    of ident * typ * string option
  | ESNote    of string

type var_types = (ident, ident, Base.String.comparator_witness) Map.t

type eprog =
  {
    estmts: estmt list;
    ealiases: (ident, typ * string option, Base.String.comparator_witness) Map.t; (* maps type aliases to their underlying type *)
    eevents: (ident, tevent, Base.String.comparator_witness) Map.t; (* maps event names to their definitions *)
    variables: (ident, var_types, Base.String.comparator_witness) Map.t; (* maps rule labels to variables used in section *)
    exceptions: (ident, (ident * Tformula.t) list, Base.String.comparator_witness) Map.t;
    labelconvention: (module Label.LabelConvention)
  }

let tempty =
  {
    estmts = [];
    ealiases = Map.empty (module String);
    eevents = Map.empty (module String);
    variables = Map.empty (module String); 
    exceptions = Map.empty (module String);
    labelconvention = (module Label.StandardConvention)
  }

let is_erule = function
  | ESRule _ -> true
  | _ -> false

let verb_of_erule = function
  | EObligation _ -> "oblige"
  | EPermission _ -> "permit"
  | EConstitutive _ -> "constitute"
  | EException _ -> "except"

let string_of_erule i erule =
  let to_string f =
    Etc.tabs (i+1) ^ Tformula.to_string f
  in
  let string_of_imp_rule verb f g =
    Printf.sprintf "%swhenever\n%s\n%s%s\n%s"
      (Etc.tabs i)
      (String.concat ~sep:"\n" (List.map ~f:to_string f))
      (Etc.tabs i)
      verb
      (String.concat ~sep:"\n" (List.map ~f:to_string g))
  in
  let string_of_exc_rule f ident =
    Printf.sprintf "%swhenever\n%s\n%sexcept \"%s\""
      (Etc.tabs i)
      (String.concat ~sep:"\n" (List.map ~f:to_string f))
      (Etc.tabs i)
      ident
  in
  match erule with
  | EObligation (f, g)
  | EPermission (f, g)
  | EConstitutive (f, g)
    -> string_of_imp_rule (verb_of_erule erule) f g
  | EException (f, ident, _) -> string_of_exc_rule f ident

let string_of_estmt eprog ?(i=0) =
  function
  | ESImport (_, idents, _) ->
     Printf.sprintf "import %s"
       (String.concat ~sep:"." idents)
  | ESSection (section_kind, _, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Etc.tabs i)
       (string_of_section_kind section_kind)
       label
       (match title with Some title -> Printf.sprintf ": \"%s\"" (of_annot title) | None -> "")
  | ESRule (_, label, type_fixes, rule, rule_type, rule_constrs, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string (of_annot s) i
          | None -> ""
      in
      let module Convention = (val eprog.labelconvention : Label.LabelConvention) in
      let qualified_name = Convention.convention.qualified_name in
      Printf.sprintf "%srule%s\n%s%s\n%s%s%s%s"
        (Etc.tabs i)
        (qualified_name label)
        (string_of_type_fixes (i+1) type_fixes)
        (string_of_erule (i+1) rule)
        (Etc.tabs i)
        (string_of_rule_type rule_type)
        (if List.is_empty rule_constrs then
          ""
        else
          Etc.tabs i ^ (string_of_rule_constrs rule_constrs))
       description
  | ESEvent (event_type, name, typed_args, pol, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
      Printf.sprintf "%s%s %s %s\n%s%s"
          (Etc.tabs i)
          (string_of_pol pol)
          (string_of_event_type event_type)
          name
          description
          (string_of_args typed_args i)
  | ESType (name, typ, doc_string) ->
      let description =
          match doc_string with
          | Some s -> make_doc_string s i
          | None -> ""
      in
     Printf.sprintf "type %s is %s%s"
       name (string_of_typ typ) description
  | ESNote text -> "note \"" ^ text ^ "\""
    
let string_of_eprog eprog =
  (* String.concat ~sep:"\n\n" (List.map prog.stmts ~f:string_of_stmt) *)
  String.concat ~sep:"\n" (List.map eprog.estmts ~f:(string_of_estmt eprog))

let print_eprog eprog =
  Stdio.printf "%s\n" (string_of_eprog eprog)
