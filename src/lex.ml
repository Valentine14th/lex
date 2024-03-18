open Core

type ident = string

type typ = TString | TInt

type pol = TCau | TSup | TObs | TCauSup | TInternal

type section_kind = Chapter | Article | Paragraph | Point

type rule =
  | Obligation   of Formula.t list * Formula.t list
  | Permission   of Formula.t list * Formula.t list
  | Constitutive of Formula.t list * Formula.t list
  | Exception    of Formula.t list * ident
    
type rule_type = Vanilla | Enforceable

type rule_constr =
  | Suppressing of ident list
  | Causing     of ident list

type stmt =
  | SImport    of string list * bool
  | SSection   of section_kind * string * string
  | SEvent     of ident * (ident * typ) list * pol
  | SRule      of string option * rule * rule_type * rule_constr list

type prog = { stmts: stmt list }

let is_rule = function
  | SRule _ -> true
  | _ -> false

let string_of_typ = function
  | TString -> "string"
  | TInt -> "int"

let string_of_pol = function
  | TCau -> "causable"
  | TSup -> "suppressable"
  | TObs -> "observable"
  | TCauSup -> "causable suppressable"
  | TInternal -> "internal"

let string_of_typed_idents (name, typ) =
  Printf.sprintf "%s : %s" name (string_of_typ typ)

let string_of_section_kind = function
  | Chapter -> "chapter"
  | Article -> "article"
  | Paragraph -> "paragraph"
  | Point -> "point"

let string_of_rule_type = function
  | Vanilla -> ""
  | Enforceable -> "enforceable "

let string_of_rule_constr = function
  | Suppressing idents -> "suppressing " ^ String.concat ~sep:", " idents
  | Causing idents -> "causing " ^ String.concat ~sep:", " idents
    
let string_of_rule_constrs rule_constrs =
  String.concat ~sep:", " (List.map ~f:string_of_rule_constr rule_constrs)

let string_of_rule i rule =
  let verb_of_rule = function
    | Obligation _ -> "oblige"
    | Permission _ -> "permit"
    | Constitutive _ -> "constitute"
    | Exception _ -> "except"
  in
  let to_string f =
    Etc.tabs (i+1) ^ Formula.to_string f
  in
  let string_of_imp_rule verb f g =
      Etc.tabs i     ^ "whenever"                       ^ "\n"
    ^ String.concat ~sep:"\n" (List.map ~f:to_string f) ^ "\n"
    ^ Etc.tabs i     ^ verb                             ^ "\n"
    ^ String.concat ~sep:"\n" (List.map ~f:to_string g)
  in
  let string_of_exc_rule f ident =
      Etc.tabs i     ^ "whenever"          ^ "\n"
    ^ String.concat ~sep:"\n" (List.map ~f:to_string f) ^ "\n"
    ^ Etc.tabs i     ^ "except \"" ^ ident ^ "\""
  in
  match rule with
  | Obligation (f, g) | Permission (f, g) | Constitutive (f, g)
    -> string_of_imp_rule (verb_of_rule rule) f g
  | Exception (f, ident) -> string_of_exc_rule f ident

let string_of_stmt ?(i=0) =
  function
  | SImport (idents, star) ->
     Printf.sprintf "import %s%s"
       (String.concat ~sep:"." idents)
       (if star then ".*" else "")
  | SSection (section_kind, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Etc.tabs i)
       (string_of_section_kind section_kind)
       label
       (if String.equal title "" then "" else Printf.sprintf ": \"%s\"" title)
  | SEvent (name, typed_idents, pol) ->
     Printf.sprintf "%sevent %s (%s) %s"
       (Etc.tabs i)
       name
       (String.concat ~sep:", " (List.map typed_idents ~f:string_of_typed_idents))
       (string_of_pol pol)
  | SRule (label, rule, rule_type, rule_constrs) ->
     Printf.sprintf "%srule%s\n%s\n%s%s%s"
       (Etc.tabs i)
       (Option.value_map label ~default:"" ~f:(fun label -> " " ^ label))
       (string_of_rule (i+1) rule)
       (Etc.tabs i)
       (string_of_rule_type rule_type)
       (if List.is_empty rule_constrs then
          ""
        else
          Etc.tabs i ^ (string_of_rule_constrs rule_constrs))
    
let string_of_prog prog =
  String.concat ~sep:"\n\n" (List.map prog.stmts ~f:string_of_stmt)
      
let print_prog prog =
  Stdio.printf "%s\n" (string_of_prog prog)

(*
  missing: algebraic data types

 *)
