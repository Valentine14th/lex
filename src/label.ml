open Core
open Lex

let debug_label = ref false
let debug = if !debug_label then Errors.debug_print ~f_name:(Some "label.ml") else ignore

(** First identifier: number, letter, etc. describing
                      the section in question (e.g. "2")
    second identifier: descriptive, title (e.g. "Material Scope") *)
type label_levels = (ident * ident option) list 

type loc =
  | LSection of section_kind * ident
  | LRule of ident
  | LNone

let string_of_loc = function
  | LSection (sk, n) -> "LSection " ^ string_of_section_kind sk ^ " \"" ^ n ^ "\""
  (* | LRule n -> "rule " ^ n *)
  | LRule n -> "LRule \"" ^ n ^ "\"" (* TODO: choose sensible string representation for rule locations *)
  | LNone -> "LNone"

type t =
  {
    law:       label_levels; (* for qualified name, this must be non-empty *)
    title:     label_levels; (* ignored for qualified name *)
    chapter:   label_levels; (* ignored for qualified name *)
    section:   label_levels; (* ignored for qualified name *)
    article:   label_levels; (* for qualified name, this must be non-empty *)
    paragraph: label_levels;
    point:     label_levels;
    subpoint:  label_levels;
    rule_id:   ident option
  }

let empty =
  {
    law       = [];
    title     = [];
    chapter   = [];
    section   = [];
    article   = [];
    paragraph = [];
    point     = [];
    subpoint  = [];
    rule_id   = None
  }

let is_empty = function
  | { law       = [];
      title     = [];
      chapter   = [];
      section   = [];
      article   = [];
      paragraph = [];
      point     = [];
      subpoint  = [];
      rule_id   = None } -> true
  | _ -> false

let qualified_label l =
  let h = match l.law with
  | h::_ -> [h]
  | [] -> []
  in { l with law = h; title = []; chapter = []; section = []; }

let lowest_level = function
  | { rule_id   = Some r; _ } -> LRule r
  | { subpoint  = levels;  _ } when List.length levels > 0 ->
     LSection (Subpoint  (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { point     = levels;  _ } when List.length levels > 0 ->
     LSection (Point     (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { paragraph = levels;  _ } when List.length levels > 0 ->
     LSection (Paragraph (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { article   = levels;  _ } when List.length levels > 0 ->
     LSection (Article   (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { section   = levels;  _ } when List.length levels > 0 ->
     LSection (Section   (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { chapter   = levels;  _ } when List.length levels > 0 ->
     LSection (Chapter   (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { title     = levels;  _ } when List.length levels > 0 ->
     LSection (Title     (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { law       = levels;  _ } when List.length levels > 0 ->
     LSection (Law       (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | _ -> LNone

let combine_with_previous = function
  | Law       i, Law       j -> Law (i+j)
  | Title     i, Title     j -> Title (i+j)
  | Chapter   i, Chapter   j -> Chapter (i+j)
  | Section   i, Section   j -> Section (i+j)
  | Article   i, Article   j -> Article (i+j)
  | Paragraph i, Paragraph j -> Paragraph (i+j)
  | Point     i, Point     j -> Point (i+j)
  | Subpoint  i, Subpoint  j -> Subpoint (i+j)
  | cur        , _           -> cur

let highest_level ?(previous_sk=Law 0) = function
  | { law       = (l,_)::_; _ } ->
     LSection (combine_with_previous (Law 0, previous_sk), l)
  | { title     = (l,_)::_; _ } ->
     LSection (combine_with_previous (Title 0, previous_sk), l)
  | { chapter   = (l,_)::_; _ } ->
     LSection (combine_with_previous (Chapter 0, previous_sk), l)
  | { section   = (l,_)::_; _ } ->
     LSection (combine_with_previous (Section 0, previous_sk), l)
  | { article   = (l,_)::_; _ } ->
     LSection (combine_with_previous (Article 0, previous_sk), l)
  | { paragraph = (l,_)::_; _ } ->
     LSection (combine_with_previous (Paragraph 0, previous_sk), l)
  | { point     = (l,_)::_; _ } ->
     LSection (combine_with_previous (Point 0, previous_sk), l)
  | { subpoint  = (l,_)::_; _ } ->
     LSection (combine_with_previous (Subpoint 0, previous_sk), l)
  | { rule_id   = Some r; _ } ->
     LRule r
  | _ -> LNone

let remove_highest_level = function
  | { law       = _::ls;  _ } as t -> { t with law       = ls   }
  | { title     = _::ls;  _ } as t -> { t with title     = ls   }
  | { chapter   = _::ls;  _ } as t -> { t with chapter   = ls   }
  | { section   = _::ls;  _ } as t -> { t with section   = ls   }
  | { article   = _::ls;  _ } as t -> { t with article   = ls   }
  | { paragraph = _::ls;  _ } as t -> { t with paragraph = ls   }
  | { point     = _::ls;  _ } as t -> { t with point     = ls   }
  | { subpoint  = _::ls;  _ } as t -> { t with subpoint  = ls   }
  | { rule_id   = Some _; _ } as t -> { t with rule_id   = None } (* not strictly necessary, will be the same as the empty case in the pattern matching *)
  | _ -> empty

let valid_rule_label pos = function
  | { law = []; _ } -> Errors.label_error "No 'law' section defined (yet). A rule must be inside of a 'law' section" pos
  | { article = []; _ } -> Errors.label_error "No 'article section defined (yet). A rule must be inside of an 'article' section" pos
  | _ -> ()

let set pos section_kind label_name l =
  try match section_kind with
      | Law i       ->
         {            law       = Util.take l.law i       @ [label_name]; rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []; chapter = []; title = []}
      | Title i     ->
         { l     with title     = Util.take l.title i     @ [label_name]; rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []; chapter = []}
      | Chapter i   ->
         { l     with chapter   = Util.take l.chapter i   @ [label_name]; rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []}
      | Section i   ->
         { l     with section   = Util.take l.section i   @ [label_name]; rule_id = None; subpoint = []; point = []; paragraph = []; article = []}
      | Article i   ->
         { l     with article   = Util.take l.article i   @ [label_name]; rule_id = None; subpoint = []; point = []; paragraph = []}
      | Paragraph i ->
         { l     with paragraph = Util.take l.paragraph i @ [label_name]; rule_id = None; subpoint = []; point = []}
      | Point i     ->
         { l     with point     = Util.take l.point i     @ [label_name]; rule_id = None; subpoint = []}
      | Subpoint i  ->
         { l     with subpoint  = Util.take l.subpoint i  @ [label_name]; rule_id = None;}
  with
  | Invalid_argument idx ->
     (* TODO: give more complete error message with a string representation of the entire label *)
     let err_msg = Printf.sprintf "wrong sub-level index '%s' in '%s'" idx (string_of_section_kind section_kind) in
     Errors.label_error err_msg pos

let set_rule_id rule_id l = { l with rule_id = rule_id }

let set_rule_id_force rule_id l = match rule_id with
  | Some _ -> { l with rule_id = rule_id }
  | _      -> { l with rule_id = Some "" }

let reference_of_label label pos =
  let rec aux sk ls = match sk, ls with
  | _          , [] -> []
  | Law       i, [(n,_)]     -> [(Law i, n)]
  | Law       i, (n,_)::rest -> (Law i, n) :: aux (Law (i+1)) rest
  | Title     i, [(n,_)]     -> [(Title i, n)]
  | Title     i, (n,_)::rest -> (Title i, n) :: aux (Title (i+1)) rest
  | Chapter   i, [(n,_)]     -> [(Chapter i, n)]
  | Chapter   i, (n,_)::rest -> (Chapter i, n) :: aux (Chapter (i+1)) rest
  | Section   i, [(n,_)]     -> [(Section i, n)]
  | Section   i, (n,_)::rest -> (Section i, n) :: aux (Section (i+1)) rest
  | Article   i, [(n,_)]     -> [(Article i, n)]
  | Article   i, (n,_)::rest -> (Article i, n) :: aux (Article (i+1)) rest
  | Paragraph i, [(n,_)]     -> [(Paragraph i, n)]
  | Paragraph i, (n,_)::rest -> (Paragraph i, n) :: aux (Paragraph (i+1)) rest
  | Point     i, [(n,_)]     -> [(Point i, n)]
  | Point     i, (n,_)::rest -> (Point i, n) :: aux (Point (i+1)) rest
  | Subpoint  i, [(n,_)]     -> [(Subpoint i, n)]
  | Subpoint  i, (n,_)::rest -> (Subpoint i, n) :: aux (Subpoint (i+1)) rest
  in
  let law       = aux (Law       0) label.law in
  let title     = aux (Title     0) label.title in
  let chapter   = aux (Chapter   0) label.chapter in
  let section   = aux (Section   0) label.section in
  let article   = aux (Article   0) label.article in
  let paragraph = aux (Paragraph 0) label.paragraph in
  let point     = aux (Point     0) label.point in
  let subpoint  = aux (Subpoint  0) label.subpoint in
  let levels    = List.rev (List.concat_map ~f:List.rev [subpoint; point; paragraph; article; section; chapter; title; law]) in
  Ref.{ sks = levels; rule = label.rule_id; pos }

let string_of_label l = Ref.to_string (reference_of_label l LexingInfo.dummy)

let qualified_name_of_law ?(exn=false) = function
  | [] -> begin match exn with
    | false -> ""
    | true -> failwith "No 'law' section defined (yet). A rule must be inside of a 'law' section"
    end
  | (name, _) :: _ -> name

let qualified_filters_of_law = function
  | [] -> []
  | (name, _) :: _ -> [(Law 0, name)]

let rec qualified_name_of_level = function
  | [] -> ""
  | (name, _) :: xs -> "(" ^ name ^ ")" ^ qualified_name_of_level xs

let qualified_name_of_level_simple xs =
  String.concat ~sep:"_" (List.map ~f:fst xs)

let qualified_filters_of_level kind_fun xs =
  List.mapi xs ~f:(fun i (name, _) -> (kind_fun i, name))

let qualified_name_of_article = function
  | [] -> ""
  | (name, _) :: xs -> name ^ qualified_name_of_level xs

let string_of_rule_id = function
  | None -> ""
  | Some s -> "#" ^ s

let string_of_rule_id2 = function
  | None -> ""
  | Some s -> s

let string_of_rule_id3 = function
  | None -> ""
  | Some s -> "-" ^ s

let qualified_name l = match
  Printf.sprintf "%s %s%s%s%s%s"
  (qualified_name_of_law l.law)
  (qualified_name_of_article l.article)
  (qualified_name_of_level l.paragraph)
  (qualified_name_of_level l.point)
  (qualified_name_of_level l.subpoint)
  (string_of_rule_id l.rule_id)
  with
  | " " -> ""
  | s -> s

let qualified_id l =
  Printf.sprintf "%s-%s-%s-%s-%s-%s"
    (Util.sanitize_string (qualified_name_of_law l.law))
    (Util.sanitize_string (qualified_name_of_article l.article))
    (Util.sanitize_string (qualified_name_of_level_simple l.paragraph))
    (Util.sanitize_string (qualified_name_of_level_simple l.point))
    (Util.sanitize_string (qualified_name_of_level_simple l.subpoint))
    (Util.sanitize_string (string_of_rule_id2 l.rule_id))

let id_of_sks sks =
  let f (s, n) = Util.sanitize_string (Lex.string_of_section_kind s ^ "-" ^ n) in
  String.concat ~sep:"-" (List.map sks ~f)
  
let reference_id l =
  let ref = reference_of_label l LexingInfo.dummy in
  id_of_sks ref.sks ^ string_of_rule_id3 ref.rule

let doc_id l =
  match l.rule_id with
  | None -> reference_id l
  | _    -> qualified_id l

let qualified_filters l =
  (qualified_filters_of_law l.law)
  @ (qualified_filters_of_level (fun i -> Article i) l.article)
  @ (qualified_filters_of_level (fun i -> Paragraph i) l.paragraph)
  @ (qualified_filters_of_level (fun i -> Point i) l.point)
  @ (qualified_filters_of_level (fun i -> Subpoint i) l.subpoint)

let full_filters l =
  (qualified_filters_of_law l.law)
  @ (qualified_filters_of_level (fun i -> Title i) l.title)
  @ (qualified_filters_of_level (fun i -> Chapter i) l.chapter)
  @ (qualified_filters_of_level (fun i -> Section i) l.section)
  @ (qualified_filters_of_level (fun i -> Article i) l.article)
  @ (qualified_filters_of_level (fun i -> Paragraph i) l.paragraph)
  @ (qualified_filters_of_level (fun i -> Point i) l.point)
  @ (qualified_filters_of_level (fun i -> Subpoint i) l.subpoint)

module Location = struct
  
  type t = ident * int * ident [@@deriving compare]

  let compare l1 l2 = match l1, l2 with
  | (sk1, i1, n1), (sk2, i2, n2) when String.equal sk1 sk2 && i1 = i2 -> String.compare n1 n2
  | (sk1, i1, _), (sk2, i2, _) when String.equal sk1 sk2 -> Int.compare i1 i2
  | (sk1, _, _), (sk2, _, _) -> String.compare sk1 sk2

  let t_of_sexp = Tuple3.t_of_sexp String.t_of_sexp Int.t_of_sexp String.t_of_sexp
  let sexp_of_t = Tuple3.sexp_of_t String.sexp_of_t Int.sexp_of_t String.sexp_of_t

  let t_of_loc = function
  | LSection (sk, n) -> 
    begin match sk with
    | Law i       -> ("law"      , i, n)
    | Title i     -> ("title"    , i, n)
    | Chapter i   -> ("chapter"  , i, n)
    | Section i   -> ("section"  , i, n)
    | Article i   -> ("article"  , i, n)
    | Paragraph i -> ("paragraph", i, n)
    | Point i     -> ("point"    , i, n)
    | Subpoint i  -> ("subpoint" , i, n)
    end
  | LRule _ | LNone -> assert false

  let string_of_t (s,i,n) = match i with
  | 0 -> s ^ " " ^ "\"" ^ n ^ "\""
  | _ -> s ^ "[" ^ string_of_int i ^ "] " ^ "\"" ^ n ^ "\""
  
end

module LocationMap = Map.Make(Location)

module RuleTree = struct
  type rule_map = (ident, int, Base.String.comparator_witness) Map.t
  type level_tree =
    | Intermediate of ((level_tree * rule_map) LocationMap.t)
    | Leaf

  let rec level_tree_to_string ?(i=0) = function
    | Leaf -> Util.tabs i ^ "Leaf"
    | Intermediate map ->
       Util.tabs i ^ "[\n" ^ Util.tabs (i+1)
       ^ String.concat ~sep:("\n" ^ Util.tabs (i+1))
           (List.map ~f:(fun (loc, (tree, rules)) ->
                Printf.sprintf "%s ->\n%s%s%s%s"
                  (Location.string_of_t loc)
                  (Util.tabs (i+2))
                  (if Map.is_empty rules then
                     "Rules: none\n"
                   else
                     Printf.sprintf "Rules:\n%s%s\n"
                       (Util.tabs (i+3))
                       (String.concat ~sep:("\n" ^ Util.tabs (i+3))
                          (List.map ~f:(fun (s, i) ->
                               Printf.sprintf "%s -> %d"
                                 (if String.is_empty s then "[unnamed]" else s) i)
                             (Map.to_alist rules))))
                  (Util.tabs (i+2))
                  (match tree with Leaf -> "Tree: none"
                                 | _ -> Printf.sprintf "Tree:\n%s\n"
                                          (level_tree_to_string ~i:(i+3) tree)))
              (Map.to_alist map))
           

  type rtref_expr = { label: t;
                      ref: Ref.t;
                      pos: LexingInfo.t }

  type s = 
    {
      label_of_rule: (int, (t * LexingInfo.t), Int.comparator_witness) Map.t;
      tree: level_tree; (* entire tree, specifically containing every level between law[0] and article[0] *)
      exceptions: (int, int list, Int.comparator_witness) Map.t; (* map from rule index i to list of rule indeces of except-rules for rule i *)
      scopes: (int, int list, Int.comparator_witness) Map.t; (* map from rule index i to list of rule indeces of scope-rules for rule i *)
    }

  let empty =
    {
      label_of_rule = Map.empty (module Int);
      tree = Leaf;
      exceptions = Map.empty (module Int);
      scopes = Map.empty (module Int);
    }

  let update_rule_map pos m k v = try Map.add_exn m ~key:k ~data:v with | _ ->
    begin match k with
    | "" -> Errors.label_error "An unlabeled rule already exists in this section, consider using labels" pos
    | _ -> Errors.label_error ("A rule with the label '" ^ k ^ "' already exists in this section") pos
    end

  let rec insert_section_in_tree ?(previous_sk=Law 0) pos tree l =
    let highest = highest_level ~previous_sk:previous_sk l in
    let lowest = lowest_level l in
    let _ = match lowest with | LRule _ -> assert false | _ -> () in
    let l' = remove_highest_level l in
    begin match highest with
    | LRule _ -> assert false
    | LNone -> tree
    | LSection (sk, _) -> 
      let key = Location.t_of_loc highest in
      begin match tree with
      | Intermediate m -> let tree', rm =
        begin match Map.find m key with 
        | Some (tree', rm) -> tree', rm
        | None -> Leaf, Map.empty (module String)
        end in
        let tree'' = insert_section_in_tree ~previous_sk:sk pos tree' l' in
        Intermediate (Map.update m key ~f:(fun _ -> (tree'', rm)))
      | Leaf -> 
        let tree' = insert_section_in_tree ~previous_sk:sk pos Leaf l' in
        let rm = Map.empty (module String) in
        Intermediate (LocationMap.of_alist_exn [(key, (tree', rm))])
      end
    end

  let rec insert_rule_in_tree ?(previous_sk=Law 0) pos tree l ri =
    let highest = highest_level ~previous_sk:previous_sk l in
    let lowest = lowest_level l in
    let _ = match lowest with | LRule _ -> () | _ -> assert false in
    let key = Location.t_of_loc highest in
    let l' = remove_highest_level l in
    let _ = match is_empty l' with
    | true -> let err_msg = match highest with
      | LNone -> assert false
      | LRule r -> "Rule '" ^ r ^ "' is outside of any section"
      | LSection _ -> assert false
      in Errors.label_error err_msg pos
    | false -> () in
    begin match is_empty (remove_highest_level l') with
    | true ->
      let highest' = highest_level l' in
      begin match  highest' with
      | LRule rn ->
        begin match tree with
        | Intermediate m -> let value =
          begin match Map.find m key with 
          | Some (tree', rm) -> tree', update_rule_map pos rm rn ri
          | None -> Leaf, Map.of_alist_exn (module String) [(rn, ri)]
          end in
          Intermediate (Map.update m key ~f:(fun _ -> value))
        | Leaf -> 
          let tree' = Leaf in
          let rm = Map.of_alist_exn (module String) [(rn, ri)] in
          Intermediate (LocationMap.of_alist_exn [(key, (tree', rm))])
        end
      | LSection _ | LNone -> assert false (* must be prevented by preceding checks *)
      end
    | false -> 
      begin match highest with
      | LRule _ | LNone -> assert false
      | LSection (sk, _) -> 
        begin match tree with
        | Intermediate m -> let tree', rm =
          begin match Map.find m key with 
          | Some (tree', rm) -> tree', rm
          | None -> Leaf, Map.empty (module String)
          end in
          let tree'' = insert_rule_in_tree ~previous_sk:sk pos tree' l' ri in
          Intermediate (Map.update m key ~f:(fun _ -> (tree'', rm)))
        | Leaf -> 
          let tree' = insert_rule_in_tree ~previous_sk:sk pos Leaf l' ri in
          let rm = Map.empty (module String) in
          Intermediate (LocationMap.of_alist_exn [(key, (tree', rm))])
        end
      end
    end

  let rec collect_rules_in_tree = function
    | Intermediate map ->
       List.concat_map (Map.to_alist map)
         ~f:(fun (_, (tree, rules)) -> collect_rules_in_tree tree @ Map.data rules)
    | Leaf -> []

  let rec infer_intermediate_levels pos map sk name intermediate_levels current_key =
    let sk_name, sk_int = match sk with
    | Law i when i > 0 -> "law", i
    | Title i -> "title", i
    | Chapter i -> "chapter", i
    | Section i -> "section", i
    | Article 0 -> "article", 0
    | _ -> assert false
    in
    let key = (sk_name, sk_int, name) in
    match Map.find map key, current_key with
    | Some _, Some k -> [map, List.append intermediate_levels [k]]
    | Some _, None -> [map, intermediate_levels]
    | None, _ ->
      let extract_maps (k, t) = match fst t with
        | Intermediate m -> Some (k, m)
        | Leaf -> None
      in
      let rec aux = function
      | [] -> assert false
      | [(k, m)] -> infer_intermediate_levels pos m sk name intermediate_levels (Some k)
      | (k, m)::ms -> List.append
                      (infer_intermediate_levels pos m sk name intermediate_levels (Some k))
                      (aux ms)
       in
      let subtrees = Map.to_alist map |> List.filter_map ~f:extract_maps in
      match subtrees with
      | [] -> []
      | _ -> aux subtrees
  
  let rec find_rules_in_tree pos label = function
  | Intermediate map ->
    let label' = remove_highest_level label in
    let highest = highest_level label in
    debug (string_of_loc highest);
    let key = Location.t_of_loc highest in
    begin match highest with
    | LNone ->
       (debug (String.concat ~sep:", " (List.map (collect_rules_in_tree (Intermediate map)) ~f:string_of_int));
       collect_rules_in_tree (Intermediate map))
    | LRule _ -> assert false
    | LSection (sk, n) ->
      let sub_maps = begin match sk with
      | Law i when i > 0 -> infer_intermediate_levels pos map sk n [] None
      | Title _
      | Chapter _
      | Section _
      | Article 0 -> infer_intermediate_levels pos map sk n [] None
      | _ -> [(map, [])]
      end in
      let map', inferred_levels = match sub_maps with
      | [] ->
        let err_msg = Printf.sprintf "Section { %s %s } was not found" (string_of_section_kind sk) n in
        Errors.reference_error err_msg pos
      | [m, ils] -> m, ils
      | _ ->
        let err_msg = Printf.sprintf "Multiple possible intermediate levels (%s) found for section { %s \"%s\" }"
                      (String.concat ~sep:", " (List.map sub_maps ~f:(fun (_, ils) -> "{ " ^ String.concat ~sep:" " (List.map ils ~f:(fun (sk, i, n) -> match i with
                        | 0 -> Printf.sprintf "%s \"%s\"" sk n
                        | _ -> Printf.sprintf "%s[%d] \"%s\"" sk i n)) ^ " }")) )
                      (string_of_section_kind sk) n in
        Errors.reference_error err_msg pos
      in
      let _ = match List.is_empty inferred_levels with
      | true -> ()
      | false ->
        let warn_msg = Printf.sprintf "Inferred intermediate levels: { %s } above { %s %s }"
                       (String.concat ~sep:", " (List.map inferred_levels ~f:(fun (sk, i, n) -> Printf.sprintf "%s[%d] \"%s\"" sk i n)))
                       (Lex.string_of_section_kind sk)
                       (n)
        in
        Errors.warning warn_msg (Some pos)
      in
      begin match highest_level label' with
      | LRule r -> begin try [Map.find_exn map' key |> snd |> (fun x -> Map.find_exn x r)]
                   with _ -> Errors.label_error ("Rule '" ^ r ^ "' not found in section '" ^ Location.string_of_t key ^ "'") pos end
      | LNone -> let tree, rules = begin try Map.find_exn map' key
                 with _ -> Errors.label_error ("Section '" ^ Location.string_of_t key ^ "' was not found") pos
                          end in
                 Map.data rules @ collect_rules_in_tree tree
      | _ -> let tree' = begin try Map.find_exn map' key |> fst
             with _ -> Errors.label_error ("Section '" ^ Location.string_of_t key ^ "' was not found") pos end
        in find_rules_in_tree pos label' tree'
      end
    end
  | Leaf -> []
  
  let add_label pos s l =
    { s with tree = insert_section_in_tree pos s.tree l }

  let add_rule pos ri label s =
    { s with tree = insert_rule_in_tree pos s.tree label ri;
             label_of_rule = Map.add_exn s.label_of_rule ~key:ri ~data:(label,pos)
    }
  
  let add_section pos label s =
    { s with tree = insert_section_in_tree pos s.tree label }

  let string_of_rule_idx s i = Ref.to_string (reference_of_label (fst (Map.find_exn s.label_of_rule i)) LexingInfo.dummy)
  let pos_of_rule_idx s i = snd (Map.find_exn s.label_of_rule i)
  let add_exception idx (refs: rtref_expr list) s =
    debug (level_tree_to_string s.tree);
    debug (String.concat ~sep:"\n" (List.map refs ~f:(fun r -> string_of_label r.label)));
    let rule_idxs = List.concat_map refs ~f:(fun ref -> find_rules_in_tree ref.pos ref.label s.tree) in
    debug (String.concat ~sep:", " (List.map rule_idxs ~f:string_of_int));
    if List.is_empty rule_idxs then Errors.warning ("No rules found for exception " ^ string_of_rule_idx s idx) None;
    { s with exceptions = List.fold rule_idxs ~init:s.exceptions ~f:(fun m r_idx -> Map.add_multi m ~key:r_idx ~data:idx) }

  let add_scope idx (refs: rtref_expr list) s =
    let rule_idxs = List.concat_map refs ~f:(fun ref -> find_rules_in_tree ref.pos ref.label s.tree) in
    if List.is_empty rule_idxs then Errors.warning ("No rules found for scope " ^ string_of_rule_idx s idx) None;
    { s with scopes = List.fold rule_idxs ~init:s.scopes ~f:(fun m r_idx -> Map.add_multi m ~key:r_idx ~data:idx) }


  let rules_with_shared_variable_scopes (s: s) =
    let rec fixpoint (m: (int, (int, 'a) Set.t, 'a) Map.t) =
      let collect_references v =
        let aux acc x = Map.find m x
            |> Option.value ~default:(Set.empty (module Int))
            |> Set.union acc in
        Set.fold v ~init:v ~f:aux in
      let m' = Map.map m ~f:collect_references in
      match Map.equal Set.equal m m' with
      | true -> m'
      | false -> fixpoint m'
    in
    let combine_exceptions_and_scopes exceptions scopes =
      let aux ~key:_ = function
        | `Left l | `Right l -> Some (Set.of_list (module Int) l)
        | `Both (l1, l2) -> Some (Set.of_list (module Int) (l1@l2))
      in
      let scopes_and_exceptions = Map.merge scopes exceptions ~f:aux in
      fixpoint scopes_and_exceptions
    in
    let class_map = combine_exceptions_and_scopes s.exceptions s.scopes in
    debug (Util.string_of_int_to_int_multi_map (Map.map class_map ~f:Set.to_list));
    let rules = Map.keys s.label_of_rule in
    debug (Util.string_of_int_list rules);
    let update_function' acc x =
      let aux x = function
        | Some s -> Set.add s x
        | None -> Set.singleton (module Int) x
      in
      Map.update acc x ~f:(aux x)
    in
    let full_map = List.fold rules ~init:class_map ~f:update_function' in
    let full_list = Map.data full_map in
    debug (Util.string_of_int_set_list full_list);
    let aux2 acc x =
      let aux1 acc' y =
        let aux0 z =
          let inter = Set.inter y z in
          debug ("y & z: " ^ Util.string_of_int_set inter);
          debug ("y: " ^ Util.string_of_int_set y);
          debug ("z: " ^ Util.string_of_int_set z);
          if (Set.is_empty inter) then z
          else Set.union y z
        in
        let acc'' = List.map acc' ~f:aux0 in
        debug ("acc'': " ^ Util.string_of_int_set_list acc'');
        List.fold acc'' ~f:Set.union ~init:y
      in
      debug ("Acc: " ^ Util.string_of_int_set_list acc);
      debug ("x: " ^ Util.string_of_int_set x);
      let intersections = List.map acc ~f:(fun a -> Set.inter x a) in
      let union_of_intersections = List.fold ~init:x ~f:Set.union intersections in
      debug ("Intersections: " ^ Util.string_of_int_set_list intersections);
      debug ("Union: " ^ Util.string_of_int_set union_of_intersections);
      match Set.equal x union_of_intersections with
      | true -> x::acc
      | false -> [aux1 acc x]
    in
    let full_list' = List.dedup_and_sort full_list ~compare:Set.compare_direct in
    let filtered_list =
      List.filter full_list'
        ~f:(fun x -> not (List.exists full_list
                            ~f:(fun y -> Set.is_subset x ~of_:y && not (Set.equal x y)))) in
    let filtered_list' = List.fold filtered_list ~init:[] ~f:aux2 in
    debug (Util.string_of_int_set_list filtered_list');
    debug (Util.string_of_int_list rules);
    assert (List.length full_list = List.length rules);
    (*assert (List.length (List.concat_map filtered_list' ~f:Set.to_list) = List.length rules);*)
    filtered_list'


end
