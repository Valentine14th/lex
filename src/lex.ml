open Core

type ident = string

type typ = TString | TInt

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

type rule =
  | Obligation   of Formula.t list * Formula.t list
  | Permission   of Formula.t list * Formula.t list
  | Constitutive of Formula.t list * Formula.t list
  | Exception    of Formula.t list * ident
    
type rule_type = Vanilla | Enforceable | Transparent

type rule_constr =
  | Suppressing of ident list
  | Causing     of ident list

type import_format =
  | ILex
  | IFormex

type stmt =
  | SImport    of Lexing.position * import_format * string list (* location points to beginning of "import" keyword *)
  | SSection   of Lexing.position * section_kind * string * string option (* location points to beginning of section label *)
  | SRule      of Lexing.position * string option * rule * rule_type * rule_constr list * string option (* location points to the beginning of the "rule" keyword *)
  | SEvent     of Lexing.position * ident * (Lexing.position * ident * ident) list * pol * string option (* location points to beginning of event identifier *)
  | SType      of Lexing.position * ident * typ (* location points to beginning of type identifier *)

type signature = ident * (ident * typ) list

type prog = { stmts: stmt list }

let compare_typs t1 t2 =
  match t1, t2 with
  | TString, TString -> true
  | TInt, TInt -> true
  | _ -> false

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
  
let string_of_rule i rule =
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
  | SRule (_, label, rule, rule_type, rule_constrs, doc_string) ->
     let description =
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> ""
      in
     Printf.sprintf "%srule%s\n%s\n%s%s%s%s"
       (Etc.tabs i)
       (Option.value_map label ~default:"" ~f:(fun label -> " " ^ label))
       (string_of_rule (i+1) rule)
       (Etc.tabs i)
       (string_of_rule_type rule_type)
       (if List.is_empty rule_constrs then
          ""
        else
          Etc.tabs i ^ (string_of_rule_constrs rule_constrs))
       description
  | SEvent (_, name, typed_args, pol, doc_string) ->
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
  | SType (_, name, typ) -> "type " ^ name ^ " is " ^ (string_of_typ typ)

let string_of_signature signature =
  match signature with
  | name, typed_idents ->
     Printf.sprintf "%s(%s)"
       name
       (String.concat ~sep:", " (List.map typed_idents ~f:string_of_typed_idents))
    
let string_of_prog prog =
  (* String.concat ~sep:"\n\n" (List.map prog.stmts ~f:string_of_stmt) *)
  String.concat ~sep:"\n" (List.map prog.stmts ~f:string_of_stmt)
      
let print_prog prog =
  Stdio.printf "%s\n" (string_of_prog prog)

let prog_to_file filename prog =
  Out_channel.write_all filename ~data:(string_of_prog prog)

(*
  missing: algebraic data types

 *)
