open Core

type ident = string

type pol = TCau | TCauObs | TSup | TObs | TCauSup | TItl

let pol_to_enftype (p: pol) = match p with
  | TCau -> Formula.EnfType.Cau
  | TObs -> Formula.EnfType.Obs
  | TSup -> Formula.EnfType.Sup
  | TCauObs -> Formula.EnfType.CauObs
  | TCauSup -> Formula.EnfType.CauSup
  | TItl -> Formula.EnfType.Itl

let enftype_to_pol (t: Formula.EnfType.t) = match t with
  | Formula.EnfType.Cau -> TCau
  | Formula.EnfType.Obs -> TObs
  | Formula.EnfType.Sup -> TSup
  | Formula.EnfType.CauObs -> TCauObs
  | Formula.EnfType.CauSup -> TCauSup
  | Formula.EnfType.Itl -> TItl
  | Formula.EnfType.Non -> assert false

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

type pattern =
  | PPresent
  | PEventually of Interval.t
  | PAlways of Interval.t
  | PUntil of Interval.t * Formula.t
  | POnce of Interval.t
  | PHistorically of Interval.t
  | PSince of Interval.t * Formula.t

type rule_type = Vanilla | Enforceable | Transparent

type rule_constr_kind =
  | CConditions
  | CCondition of int
  | CEffects
  | CExceptions
  | CScopes
  | CEvent of string

type rule_constr =
  | Suppressing of rule_constr_kind list
  | Causing     of rule_constr_kind list

type rule =
  | Obligation   of (Lexing.position * Formula.t) list * pattern * (Lexing.position * Formula.t) list * pattern * rule_type * rule_constr list
  | Permission   of (Lexing.position * Formula.t) list * pattern * (Lexing.position * Formula.t) list * pattern * rule_type * rule_constr list
  | Constitutive of (Lexing.position * Formula.t) list * pattern * (Lexing.position * Formula.t) list
  | Exception    of (Lexing.position * Formula.t) list * pattern * (Lexing.position * reference) list
  | ExceptionC   of (Lexing.position * Formula.t) list * pattern * (Lexing.position * reference) list * (Lexing.position * Formula.t) list
  | Scope        of (Lexing.position * Formula.t) list * pattern * (Lexing.position * reference) list

type import_format =
  | ILex
  | IFormex
  | IAkomaNtoso

type event_syntax =
  | Standard
  | Functional
  | Variable

type event_type = Event of bool * event_syntax | Predicate

type stmt =
  | SImport    of Lexing.position * import_format * string list (* location points to beginning of "import" keyword *)
  | SSection   of Lexing.position * section_kind * string * string option (* location points to beginning of section label *)
  | SRule      of Lexing.position * string option * (ident * Formula.TypeTerm.t) list * rule * string option (* location points to the beginning of the "rule" keyword *)
  | SEvent     of Lexing.position * event_type * ident * (Lexing.position * ident * Formula.TypeTerm.t) list * pol * string option (* location points to beginning of event identifier *)
  | SType      of Lexing.position * ident * (Formula.TypeTerm.t option) * string option (* location points to beginning of type identifier *)
  | SFunction  of Lexing.position * ident * (ident * Formula.TypeTerm.t) list * Formula.TypeTerm.t * string option
  | SNote      of Lexing.position * string

type signature = ident * (ident * Dom.tt) list

type prog = { stmts: stmt list }

let compare_typs t1 t2 =
  match t1, t2 with
  | Dom.TStr, Dom.TStr
  | TInt, TInt
  | TFloat, TFloat -> true
  | _ -> false

let is_rule = function
  | SRule _ -> true
  | _ -> false

let string_of_pol = function
  | TCau -> "causable"
  | TSup -> "suppressable"
  | TObs -> "observable"
  | TCauObs -> "causable observable"
  | TCauSup -> "causable suppressable"
  | TItl -> "internal"

let string_of_typed_idents (name, tt) =
  Printf.sprintf "%s : %s" name (Dom.string_of_tt tt)

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

let string_of_rule_constr_kind = function
  | CConditions -> "conditions"
  | CCondition i -> "condition[" ^ string_of_int i ^ "]"
  | CEffects -> "effects"
  | CExceptions -> "exceptions"
  | CScopes -> "scopes"
  | CEvent s -> s

let string_of_rule_constr = function
  | Suppressing cs -> "suppressing " ^ String.concat ~sep:", " (List.map cs ~f:string_of_rule_constr_kind)
  | Causing cs -> "causing " ^ String.concat ~sep:", " (List.map cs ~f:string_of_rule_constr_kind)
    
let string_of_rule_constrs rule_constrs =
  String.concat ~sep:", " (List.map ~f:string_of_rule_constr rule_constrs)

let verb_of_rule = function
  | Obligation _ -> "oblige"
  | Permission _ -> "permit"
  | Constitutive _ -> "constitute"
  | Exception _ 
    | ExceptionC _ -> "except"
  | Scope _ -> "scope"

let string_of_reference (rs, rule) =
  let rule_id = match rule with
    | Some r -> " rule \"" ^ r ^ "\""
    | None ->  ""
  in
  let string_of_section_kind_and_name (s, n) = string_of_section_kind s ^ " \"" ^ n ^ "\"" in
   String.concat ~sep:" " (List.map ~f:string_of_section_kind_and_name rs) ^ rule_id 

let string_of_pattern = function
  | PPresent -> ""
  | PEventually i -> " eventually " ^ Interval.to_string i 
  | PAlways i -> " always in the future " ^ Interval.to_string i 
  | PUntil (i, f) -> " eventually delaying if " ^ Formula.to_string f ^ " " ^ Interval.to_string i
  | POnce i -> " once " ^ Interval.to_string i
  | PHistorically i -> " always in the past " ^ Interval.to_string i
  | PSince (i, f) -> " always since " ^ Formula.to_string f ^ " " ^ Interval.to_string i

let string_of_rule i rule =
  let to_string f = Etc.tabs (i+1) ^ Formula.to_string f in
  let string_of_formula_list f =
    String.concat ~sep:"\n" (List.map ~f:(fun (_,f') -> to_string f') f) ^ "\n" in
  (*let string_of_formula_list_list fs =
    String.concat ~sep:("\n" ^ Etc.tabs i ^ "or\n") (List.map ~f:string_of_formula_list fs) in*)
  let string_of_imp_rule verb f p g q rcs rt =
    Etc.tabs i     ^ "whenever" ^ string_of_pattern p ^ "\n"
    ^ string_of_formula_list f ^ "\n"
    ^ Etc.tabs i   ^ verb       ^ string_of_pattern q ^ "\n"
    ^ string_of_formula_list g
    ^ Etc.tabs i ^ string_of_rule_type rt (* TODO: check that this prints the rule_type correctly *)
    ^ (if List.is_empty rcs then "" (* TODO: check that this prints the rule_constr list correctly *)
      else Etc.tabs i ^ (string_of_rule_constrs rcs))
  in
  let string_of_cons_rule verb f p g =
    Etc.tabs i     ^ "whenever" ^ string_of_pattern p ^ "\n"
    ^ string_of_formula_list f ^ "\n"
    ^ Etc.tabs i   ^ verb      ^ "\n"
    ^ string_of_formula_list g
  in
  let string_of_exc_rule verb f p rs =
    Etc.tabs i     ^ "whenever"  ^ string_of_pattern p ^ "\n"
    ^ string_of_formula_list f ^ "\n"
    ^ Etc.tabs i   ^ verb
    ^ String.concat ~sep:"\n" (List.map ~f:(fun (_,r') -> string_of_reference r') rs)
  in
  let string_of_excc_rule verb f p rs g =
    Etc.tabs i     ^ "whenever"  ^ string_of_pattern p ^ "\n"
    ^ string_of_formula_list f ^ "\n"
    ^ Etc.tabs i   ^ verb
    ^ String.concat ~sep:"\n" (List.map ~f:(fun (_,r') -> string_of_reference r') rs)
    ^ Etc.tabs i   ^ "constitute"
    ^ string_of_formula_list g
  in
  match rule with
  | Obligation (f, p, g, q, rt, rcs) | Permission (f, p, g, q, rt, rcs)
    -> string_of_imp_rule (verb_of_rule rule) f p g q rcs rt
  | Constitutive (f, p, g)
    -> string_of_cons_rule (verb_of_rule rule) f p g
  | Exception (f, p, references) | Scope (f, p, references)
    -> string_of_exc_rule (verb_of_rule rule) f p references
  | ExceptionC (f, p, references, g)
    -> string_of_excc_rule (verb_of_rule rule) f p references g

let string_of_args args i = 
    let string_of_arg (_, name, typ_alias) = 
      Printf.sprintf "%s%s : %s" (Etc.tabs (i+1)) name (Formula.TypeTerm.value_to_string typ_alias)
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

let string_of_event_syntax = function
  | Functional -> " functional "
  | Variable -> " variable "
  | Standard -> ""

let string_of_event_type = function
  | Event (b, sy) -> (if b then "external " else "") ^ string_of_event_syntax sy ^ "event"
  | Predicate -> "predicate"

let string_of_type_fixes i = function
  | [] -> ""
  | type_fixes ->
     let f (ident, typ) = Printf.sprintf "%s : %s" ident (Formula.TypeTerm.value_to_string typ) in
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
  | SRule (_, label, type_fixes, rule, doc_string) ->
     let description = 
       match doc_string with
       | Some s -> "\n" ^ make_doc_string s i
       | None -> ""
      in
     Printf.sprintf "%srule%s\n%s%s\n%s"
       (Etc.tabs i)
       (Option.value_map label ~default:"" ~f:(fun label -> " " ^ label))
       (string_of_type_fixes (i+1) type_fixes)
       (string_of_rule (i+1) rule)
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
       | None -> "" in
     let typ_string =
       match typ with
       | Some tt -> " is " ^ Formula.TypeTerm.to_string tt
       | None -> "" in
     Printf.sprintf "%stype %s%s%s"
       (Etc.tabs i) name typ_string description
  | SFunction (_, name, typed_args, return_typ, doc_string) ->
     let description =
          match doc_string with
          | Some s -> "\n" ^ make_doc_string s i
          | None -> ""
     in
     let f (ident, typ) = Printf.sprintf "%s : %s" ident (Formula.TypeTerm.value_to_string typ) in
     Printf.sprintf "%sfunction %s(%s) -> %s%s"
       (Etc.tabs i)
       name
       (String.concat ~sep:", " (List.map typed_args ~f))
       (Formula.TypeTerm.to_string return_typ)
       description
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

let unpack_functional tevents trm' = function
  | Formula.Term.App (f, trms) ->
     (match Map.find tevents f with
      | Some (Event (_, Functional) as et, _, _, _) ->
         Some (f, trms @ [trm'], et)
      | _ -> None)
  | _ -> None

let unpack_variable tevents trm' = function
  | Formula.Term.Var x ->
     (match Map.find tevents x with
      | Some (Event (_, Variable) as et, _, _, _) ->
         Some (x, [trm'], et)
      | _ -> None)
  | _ -> None

let unpack_special_eq tevents trm trm' =
  List.find_map
    [unpack_functional tevents trm trm';
     unpack_functional tevents trm' trm;
     unpack_variable tevents trm trm';
     unpack_variable tevents trm' trm]
    ~f:(fun x -> x)
