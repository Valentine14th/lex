open Core

type ident = string

type typ = TString | TInt | TFloat

type pol = TCau | TSup | TObs | TCauSup | TInternal

type section_kind =
  | Law       of int
  | Title     of int
  | Chapter   of int
  | Section   of int
  | Article   of int
  | Paragraph of int
  | Point     of int
  | Subpoint  of int

type reference = (section_kind * ident) list * ident option

let equal_section_kind kind kind' =
  match kind, kind' with
  | Law i, Law i'
  | Title i, Title i'
  | Chapter i, Chapter i'
  | Section i, Section i'
  | Article i, Article i'
  | Paragraph i, Paragraph i'
  | Point i, Point i' 
  | Subpoint i, Subpoint i' when i = i' -> true
  | _, _ -> false

let compare_section_kind kind kind' =
  let rank = function
    | Law i       -> (7, -i)
    | Title i     -> (6, -i)
    | Chapter i   -> (5, -i)
    | Section i   -> (4, -i)
    | Article i   -> (3, -i)
    | Paragraph i -> (2, -i)
    | Point i     -> (1, -i)
    | Subpoint i  -> (0, -i)
  in
  let compare_tuple (a, b) (a', b') =
    match Int.compare a a' with
    | 0 -> Int.compare b b'
    | n -> n
  in
  compare_tuple (rank kind) (rank kind')

type rule =
  | Obligation   of (Lexing.position * Formula.t) list * (Lexing.position * Formula.t) list
  | Permission   of (Lexing.position * Formula.t) list * (Lexing.position * Formula.t) list
  | Constitutive of (Lexing.position * Formula.t) list * (Lexing.position * Formula.t) list
  | Exception    of (Lexing.position * Formula.t) list * (Lexing.position * reference) list
  | Scope        of (Lexing.position * Formula.t) list * (Lexing.position * reference) list

type rule_type = Vanilla | Enforceable | Transparent

type rule_constr =
  | Suppressing of ident list
  | Causing     of ident list

type import_format =
  | ILex
  | IFormex
  | IAkomaNtoso

type event_type = Event | Predicate

type stmt =
  | SImport    of Lexing.position * import_format * string list (* location points to beginning of "import" keyword *)
  | SSection   of Lexing.position * section_kind * string * string option (* location points to beginning of section label *)
  | SRule      of Lexing.position * string option * (ident * ident) list * rule * rule_type * rule_constr list * string option (* location points to the beginning of the "rule" keyword *)
  | SEvent     of Lexing.position * event_type * ident * (Lexing.position * ident * ident) list * pol * string option (* location points to beginning of event identifier *)
  | SType      of Lexing.position * ident * typ * string option (* location points to beginning of type identifier *)
  | SNote      of Lexing.position * string

type signature = ident * (ident * typ) list

type prog = { stmts: stmt list }

let compare_typs t1 t2 =
  match t1, t2 with
  | TString, TString
  | TInt, TInt
  | TFloat, TFloat -> true
  | _ -> false

let is_rule = function
  | SRule _ -> true
  | _ -> false

let string_of_typ = function
  | TString -> "string"
  | TInt -> "int"
  | TFloat -> "float"

let string_of_pol = function
  | TCau -> "causable"
  | TSup -> "suppressable"
  | TObs -> "observable"
  | TCauSup -> "causable suppressable"
  | TInternal -> "internal"

let string_of_typed_idents (name, typ) =
  Printf.sprintf "%s : %s" name (string_of_typ typ)

let string_of_label_level = function
  | 0 -> ""
  | i -> Printf.sprintf "[%d]" i

let string_of_section_kind = function
  | Law i -> "law" ^ string_of_label_level i
  | Title i -> "title" ^ string_of_label_level i
  | Chapter i -> "chapter" ^ string_of_label_level i
  | Section i -> "section" ^ string_of_label_level i
  | Article i -> "article" ^ string_of_label_level i
  | Paragraph i -> "paragraph" ^ string_of_label_level i
  | Point i -> "point" ^ string_of_label_level i
  | Subpoint i -> "subpoint" ^ string_of_label_level i

let string_of_rule_type = function
  | Vanilla -> ""
  | Enforceable -> "enforceable "
  | Transparent -> "transparently enforceable "

let string_of_rule_constr = function
  | Suppressing idents -> "suppressing " ^ String.concat ~sep:", " idents
  | Causing idents -> "causing " ^ String.concat ~sep:", " idents
    
let string_of_rule_constrs rule_constrs =
  String.concat ~sep:", " (List.map ~f:string_of_rule_constr rule_constrs)

let verb_of_rule = function
  | Obligation _ -> "oblige"
  | Permission _ -> "permit"
  | Constitutive _ -> "constitute"
  | Exception _ -> "except"
  | Scope _ -> "scope"

let string_of_reference (rs, rule) =
  let rule_id = match rule with
    | Some r -> "rule \"" ^ r ^ "\""
    | None ->  ""
  in
  let string_of_section_kind_and_name (s, n) = string_of_section_kind s ^ " \"" ^ n ^ "\"" in
  "{ " ^ String.concat ~sep:" " (List.map ~f:string_of_section_kind_and_name rs) ^ rule_id ^ " }"

let string_of_rule i rule =
  let to_string f =
    Etc.tabs (i+1) ^ Formula.to_string f
  in
  let string_of_imp_rule verb f g =
      Etc.tabs i     ^ "whenever"                       ^ "\n"
    ^ String.concat ~sep:"\n" (List.map ~f:(fun (_,f') -> to_string f') f) ^ "\n"
    ^ Etc.tabs i     ^ verb                             ^ "\n"
    ^ String.concat ~sep:"\n" (List.map ~f:(fun (_,f') -> to_string f') g)
  in
  let string_of_exc_rule verb f rs =
      Etc.tabs i     ^ "whenever"          ^ "\n"
    ^ String.concat ~sep:"\n" (List.map ~f:(fun (_,f') -> to_string f') f) ^ "\n"
    ^ Etc.tabs i     ^ verb
    ^ String.concat ~sep:"\n" (List.map ~f:(fun (_,r') -> string_of_reference r') rs)
  in
  match rule with
  | Obligation (f, g) | Permission (f, g) | Constitutive (f, g)
    -> string_of_imp_rule (verb_of_rule rule) f g
  | Exception (f, references) | Scope (f, references)
    -> string_of_exc_rule (verb_of_rule rule) f references

let string_of_args args i = 
    let string_of_arg (_, name, typ_alias) = 
      Printf.sprintf "%s%s : %s" (Etc.tabs (i+1)) name typ_alias
    in
    String.concat ~sep:"\n" (List.map args ~f:string_of_arg)

let make_doc_string ds i = 
    let lines = String.split ~on:'\n' ds in
    let indented = List.map lines ~f:(fun l -> Etc.tabs i ^ l) in
    Etc.tabs (i + 1) ^ "\"\"\"" ^ String.concat ~sep:"\n" indented ^ Etc.tabs i ^ "\"\"\"\n"

let string_of_import_format = function
  | ILex -> ""
  | IFormex -> " formex "
  | IAkomaNtoso -> " akomaNtoso "

let string_of_event_type = function
  | Event -> "event"
  | Predicate -> "predicate"

let string_of_type_fixes i = function
  | [] -> ""
  | type_fixes ->
     let f (ident, typ) = Printf.sprintf "%s : %s" ident typ in
     Printf.sprintf "%sfix\n%s%s\n"
       (Etc.tabs i)
       (Etc.tabs (i+1))
       (String.concat (List.map type_fixes ~f) ~sep:("\n" ^ Etc.tabs (i+1)))

let string_of_stmt ?(i=0) =
  function
  | SImport (_, import_format, idents) ->
     Printf.sprintf "import %s%s"
       (string_of_import_format import_format)
       (String.concat ~sep:"." idents)
  | SSection (_, section_kind, label, title) ->
     Printf.sprintf "%s%s \"%s\"%s"
       (Etc.tabs i)
       (string_of_section_kind section_kind)
       label
       (match title with Some title -> Printf.sprintf " \"%s\"" title | None -> "")
  | SRule (_, label, type_fixes, rule, rule_type, rule_constrs, doc_string) ->
     let description = 
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> ""
      in
     Printf.sprintf "%srule%s\n%s%s\n%s%s%s%s"
       (Etc.tabs i)
       (Option.value_map label ~default:"" ~f:(fun label -> " " ^ label))
       (string_of_type_fixes (i+1) type_fixes)
       (string_of_rule (i+1) rule)
       (Etc.tabs i)
       (string_of_rule_type rule_type)
       (if List.is_empty rule_constrs then
          ""
        else
          Etc.tabs i ^ (string_of_rule_constrs rule_constrs))
       description
  | SEvent (_, event_type, name, typed_args, pol, doc_string) ->
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
  | SType (_, name, typ, doc_string) ->
     let description =
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> ""
     in
     Printf.sprintf "type %s is %s%s"
       name (string_of_typ typ) description
  | SNote (_, text) -> "note \"" ^ text ^ "\""

let string_of_signature signature =
  match signature with
  | name, typed_idents ->
     Printf.sprintf "%s(%s)"
       name
       (String.concat ~sep:", " (List.map typed_idents ~f:string_of_typed_idents))
    
let string_of_prog prog =
  String.concat ~sep:"\n" (List.map prog.stmts ~f:string_of_stmt)
      
let print_prog prog =
  Stdio.printf "%s\n" (string_of_prog prog)

let prog_to_file filename prog =
  Out_channel.write_all filename ~data:(string_of_prog prog)

(*
  missing: algebraic data types

 *)
