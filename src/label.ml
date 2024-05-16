open Core
open Lex

(** First identifier: number, letter, etc. describing
                      the section in question (e.g. "2")
    second identifier: descriptive, title (e.g. "Material Scope") *)
type label_levels = (ident * ident option) list 

type location =
  | LSection of section_kind * ident
  | LRule of ident
  | LNone

let string_of_location = function
  | LSection (sk, n) -> string_of_section_kind sk ^ " \"" ^ n ^ "\""
  (* | LRule n -> "rule " ^ n *)
  | LRule n -> n (* TODO: choose sensible string representation for rule locations *)
  | LNone -> ""

type t =
  {
    law: label_levels; (* for qualified name, this must be non-empty *)
    title: label_levels; (* ignored for qualified name *)
    chapter: label_levels; (* ignored for qualified name *)
    section: label_levels; (* ignored for qualified name *)
    article: label_levels; (* for qualified name, this must be non-empty *)
    paragraph: label_levels;
    point: label_levels;
    subpoint: label_levels;
    rule_id: ident option
  }

let empty =
  {
    law = [];
    title = [];
    chapter = [];
    section = [];
    article = [];
    paragraph = [];
    point = [];
    subpoint = [];
    rule_id = None
  }

let is_empty = function
  | { law = []; title = []; chapter = []; section = []; article = []; paragraph = []; point = []; subpoint = []; rule_id = None } -> true
  | _ -> false

let qualified_label l =
  let h =  match List.hd l.law with
  | Some h -> [h]
  | None -> []
  in {l with law = h; title = []; chapter = []; section = []; }

let lowest_level = function
  | { rule_id = Some r; _ } -> LRule r
  | { subpoint = levels;  _ } when List.length levels > 0 -> LSection (Subpoint (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { point = levels;  _ } when List.length levels > 0 -> LSection (Point (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { paragraph = levels;  _ } when List.length levels > 0 -> LSection (Paragraph (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { article = levels;  _ } when List.length levels > 0 -> LSection (Article (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { section = levels;  _ } when List.length levels > 0 -> LSection (Section (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { chapter = levels;  _ } when List.length levels > 0 -> LSection (Chapter (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { title = levels;  _ } when List.length levels > 0 -> LSection (Title (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | { law = levels;  _ } when List.length levels > 0 -> LSection (Law (List.length levels - 1), fst (List.hd_exn (List.rev levels)))
  | _ -> LNone

let combine_with_previous = function
  | Law i, Law j -> Law (i+j)
  | Title i, Title j -> Title (i+j)
  | Chapter i, Chapter j -> Chapter (i+j)
  | Section i, Section j -> Section (i+j)
  | Article i, Article j -> Article (i+j)
  | Paragraph i, Paragraph j -> Paragraph (i+j)
  | Point i, Point j -> Point (i+j)
  | Subpoint i, Subpoint j -> Subpoint (i+j)
  | cur, _ -> cur

let highest_level ?(previous_sk=Law 0) = function
  | { law = (l,_)::_; _ } -> LSection (combine_with_previous (Law 0, previous_sk), l)
  | { title = (l,_)::_; _ } -> LSection (combine_with_previous (Title 0, previous_sk), l)
  | { chapter = (l,_)::_; _ } -> LSection (combine_with_previous (Chapter 0, previous_sk), l)
  | { section = (l,_)::_; _ } -> LSection (combine_with_previous (Section 0, previous_sk), l)
  | { article = (l,_)::_; _ } -> LSection (combine_with_previous (Article 0, previous_sk), l)
  | { paragraph = (l,_)::_; _ } -> LSection (combine_with_previous (Paragraph 0, previous_sk), l)
  | { point = (l,_)::_; _ } -> LSection (combine_with_previous (Point 0, previous_sk), l)
  | { subpoint = (l,_)::_; _ } -> LSection (combine_with_previous (Subpoint 0, previous_sk), l)
  | { rule_id = Some r; _ } -> LRule r
  | _ -> LNone

let remove_highest_level = function
  | { law = _::ls; _ } as t -> { t with law = ls }
  | { title = _::ls; _ } as t-> { t with title = ls }
  | { chapter = _::ls; _ } as t-> { t with chapter = ls }
  | { section = _::ls; _ } as t-> { t with section = ls }
  | { article = _::ls; _ } as t-> { t with article = ls }
  | { paragraph = _::ls; _ } as t-> { t with paragraph = ls }
  | { point = _::ls; _ } as t-> { t with point = ls }
  | { subpoint = _::ls; _ } as t-> { t with subpoint = ls }
  | { rule_id = Some _; _ } as t-> { t with rule_id = None } (* not strictly necessary, will be the same as the empty case in the pattern matching *)
  | _ -> empty

let valid_rule_label pos = function
  | { law = []; _ } -> Util.label_error "No 'law' section defined (yet). A rule must be inside of a 'law' section" pos
  | { article = []; _ } -> Util.label_error "No 'article section defined (yet). A rule must be inside of an 'article' section" pos
  | _ -> ()

let set pos section_kind label_name l = try match section_kind with
    | Law i       -> {            law       = Util.take l.law i @ [label_name];       rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []; chapter = []; title = []}
    | Title i     -> { l     with title     = Util.take l.title i @ [label_name];     rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []; chapter = []}
    | Chapter i   -> { l     with chapter   = Util.take l.chapter i @ [label_name];   rule_id = None; subpoint = []; point = []; paragraph = []; article = []; section = []}
    | Section i   -> { l     with section   = Util.take l.section i @ [label_name];   rule_id = None; subpoint = []; point = []; paragraph = []; article = []}
    | Article i   -> { l     with article   = Util.take l.article i @ [label_name];   rule_id = None; subpoint = []; point = []; paragraph = []}
    | Paragraph i -> { l     with paragraph = Util.take l.paragraph i @ [label_name]; rule_id = None; subpoint = []; point = []}
    | Point i     -> { l     with point     = Util.take l.point i @ [label_name];     rule_id = None; subpoint = []}
    | Subpoint i  -> { l     with subpoint  = Util.take l.subpoint i @ [label_name];  rule_id = None;}
  with
    | Invalid_argument idx ->
      (* TODO: give more complete error message with a string representation of the entire label *)
      let err_msg = Printf.sprintf "wrong sub-level index '%s' in '%s'" idx (string_of_section_kind section_kind) in
      Util.label_error err_msg pos

let set_rule_id rule_id l = { l with rule_id = rule_id }

let set_rule_id_force rule_id l = match rule_id with
  | Some _ -> { l with rule_id = rule_id }
  | _      -> { l with rule_id = Some "" }

let reference_of_label label =
  let aux sk acc (n,_) = match sk with
  | Law i -> (Law (i+1), n) :: acc
  | Title i -> (Title (i+1), n) :: acc
  | Chapter i -> (Chapter (i+1), n) :: acc
  | Section i -> (Section (i+1), n) :: acc
  | Article i -> (Article (i+1), n) :: acc
  | Paragraph i -> (Paragraph (i+1), n) :: acc
  | Point i -> (Point (i+1), n) :: acc
  | Subpoint i -> (Subpoint (i+1), n) :: acc
  in
  let law = List.fold label.law ~init:[] ~f:(aux (Law 0)) in
  let title = List.fold label.title ~init:law ~f:(aux (Title 0)) in
  let chapter = List.fold label.chapter ~init:title ~f:(aux (Chapter 0)) in
  let section = List.fold label.chapter ~init:chapter ~f:(aux (Section 0)) in
  let article = List.fold label.chapter ~init:section ~f:(aux (Article 0)) in
  let paragraph = List.fold label.chapter ~init:article ~f:(aux (Paragraph 0)) in
  let point = List.fold label.chapter ~init:paragraph ~f:(aux (Point 0)) in
  let subpoint = List.fold label.chapter ~init:point ~f:(aux (Subpoint 0)) in
  let levels = List.rev subpoint in
  levels, label.rule_id

let string_of_label l = string_of_reference (reference_of_label l)

let qualified_name_of_law = function
  | [] -> ""
  | (name, _) :: _ -> name

let qualified_filters_of_law = function
  | [] -> []
  | (name, _) :: _ -> [(Law 0, name)]

let rec qualified_name_of_level = function
  | [] -> ""
  | (name, _) :: xs -> "(" ^ name ^ ")" ^ qualified_name_of_level xs

let qualified_name_of_level_simple xs = String.concat ~sep:"_" (List.map ~f:fst xs)

let qualified_filters_of_level kind_fun xs =
  List.mapi xs ~f:(fun i (name, _) -> (kind_fun i, name))

let qualified_name_of_article = function
  | [] -> ""
  | (name, _) :: xs -> name ^ qualified_name_of_level xs

let string_of_rule_id = function
  | None -> ""
  | Some s -> "#" ^ s

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
  (qualified_name_of_law l.law)
  (qualified_name_of_article l.article)
  (qualified_name_of_level_simple l.paragraph)
  (qualified_name_of_level_simple l.point)
  (qualified_name_of_level_simple l.subpoint)
  (string_of_rule_id l.rule_id)

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

module RuleTree = struct

  type rule_map = (ident, int, Base.String.comparator_witness) Map.t
  type level_tree =
    | Intermediate of (ident, level_tree * rule_map, Base.String.comparator_witness) Map.t
    | Leaf

  let update_rule_map pos m k v = try Map.add_exn m ~key:k ~data:v with | _ ->
    begin match k with
    | "" -> Util.label_error "An unlabeled rule already exists in this section, consider using labels" pos
    | _ -> Util.label_error ("A rule with the label '" ^ k ^ "' already exists in this section") pos
    end

  let rec insert_section_in_tree ?(previous_sk=Law 0) pos tree l =
    let highest = highest_level ~previous_sk:previous_sk l in
    let lowest = lowest_level l in
    let _ = match lowest with | LRule _ -> assert false | _ -> () in
    let key = string_of_location highest in
    let l' = remove_highest_level l in
    begin match highest with
    | LRule _ -> assert false
    | LNone -> tree
    | LSection (sk, _) -> 
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
        Intermediate (Map.of_alist_exn (module String) [(key, (tree', rm))])
      end
    end

  let rec insert_rule_in_tree ?(previous_sk=Law 0) pos tree l ri =
    let highest = highest_level ~previous_sk:previous_sk l in
    let lowest = lowest_level l in
    let _ = match lowest with | LRule _ -> () | _ -> assert false in
    let key = string_of_location highest in
    let l' = remove_highest_level l in
    let _ = match is_empty l' with
    | true -> let err_msg = match highest with
      | LNone -> assert false
      | LRule r -> "Rule '" ^ r ^ "' is outside of any section"
      | LSection _ -> assert false
      in Util.label_error err_msg pos
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
          Intermediate (Map.of_alist_exn (module String) [(key, (tree', rm))])
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
          Intermediate (Map.of_alist_exn (module String) [(key, (tree', rm))])
        end
      end
    end

  let rec collect_rules_in_tree = function
  | Intermediate map -> Map.fold map ~init:[] ~f:(fun ~key:_ ~data:(tree, rm) acc -> collect_rules_in_tree tree @  Map.data rm @ acc)
  | Leaf -> []
  
  let rec find_rules_in_tree pos label = function
  | Intermediate map ->
    let label' = remove_highest_level label in
    let highest = highest_level label in
    let key = string_of_location highest in
    begin match highest with
    | LNone -> collect_rules_in_tree (Intermediate map)
    | LRule _ -> assert false
    | LSection (_, _) ->
      begin match highest_level label' with
      | LRule r -> begin try [Map.find_exn map key |> snd |> (fun x -> Map.find_exn x r)]
                   with _ -> Util.label_error ("Rule '" ^ r ^ "' not found in section '" ^ key ^ "'") pos end
      | _ ->
        let tree' = begin try Map.find_exn map key |> fst
                    with _ -> Util.label_error ("Section '" ^ key ^ "' was not found") pos end
        in find_rules_in_tree pos label' tree'
      end
    end
  | Leaf -> []
  
  type s = 
    {
      label_of_rule: (int, t, Int.comparator_witness) Map.t;
      full_tree: level_tree; (* entire tree, specifically containing every level between law[0] and article[0] *)
      qualified_tree: level_tree; (* smaller map, going from law[0] directly to article[0] *)
      exceptions: (int, int list, Int.comparator_witness) Map.t; (* map from rule index i to list of rule indeces of except-rules for rule i *)
      scopes: (int, int list, Int.comparator_witness) Map.t; (* map from rule index i to list of rule indeces of scope-rules for rule i *)
    }

  let empty =
    {
      label_of_rule = Map.empty (module Int);
      full_tree = Leaf;
      qualified_tree = Leaf;
      exceptions = Map.empty (module Int);
      scopes = Map.empty (module Int);
    }
  
  let add_label pos s l =
    { s with full_tree = insert_section_in_tree pos s.full_tree l;
             qualified_tree = insert_section_in_tree pos s.qualified_tree (qualified_label l)
    }

  let add_rule pos ri label s =
    { s with full_tree = insert_rule_in_tree pos s.full_tree label ri;
             qualified_tree = insert_rule_in_tree pos s.qualified_tree (qualified_label label) ri;
             label_of_rule = Map.add_exn s.label_of_rule ~key:ri ~data:label
    }
  
  let add_section pos label s =
    { s with full_tree = insert_section_in_tree pos s.full_tree label;
             qualified_tree = insert_section_in_tree pos s.qualified_tree (qualified_label label);
    }

  let add_exception idx refs s =
    let rule_idxs = List.concat_map refs ~f:(fun (pos, l) -> find_rules_in_tree pos l s.full_tree) in
    { s with exceptions = List.fold rule_idxs ~init:s.exceptions ~f:(fun m r_idx -> Map.add_multi m ~key:idx ~data:r_idx) }

  let add_scope idx refs s =
    let rule_idxs = List.concat_map refs ~f:(fun (pos, l) -> find_rules_in_tree pos l s.full_tree) in
    { s with scopes = List.fold rule_idxs ~init:s.scopes ~f:(fun m r_idx -> Map.add_multi m ~key:idx ~data:r_idx) }


  let rules_with_shared_variables s =
    let rec fixpoint m =
      let m' = Map.map m ~f:(fun v -> Set.fold v ~init:v ~f:(fun acc x -> 
        let values = Map.find m x |> Option.value ~default:(Set.empty (module Int)) in
        Set.union acc values))
      in
      match Map.equal Set.equal m m' with
      | true -> m'
      | false -> fixpoint m'
    in
    let aux exceptions scopes =
      let scopes_and_exceptions = Map.merge scopes exceptions ~f:(fun ~key:_ -> function
        | `Left l | `Right l -> Some (Set.of_list (module Int) l)
        | `Both (l1, l2) -> Some (Set.of_list (module Int) (l1@l2))
      ) in
      fixpoint scopes_and_exceptions
    in
    let class_map = aux s.exceptions s.scopes in
    let rules = Map.keys s.label_of_rule in
    let full_map = List.fold rules ~init:class_map ~f:(fun acc x -> Map.update acc x ~f:(function
      | Some s -> Set.add s x
      | None -> Set.singleton (module Int) x))
    in
    let full_list = Map.data full_map in
    let filtered_list = List.fold full_list ~init:[] ~f:(fun acc x -> match Set.length (List.fold acc ~init:x ~f:(fun acc' y -> Set.union acc' y)) with | 0 -> x::acc | _ -> acc) in
    assert (List.length full_list = List.length rules);
    assert (List.length (List.concat_map filtered_list ~f:Set.to_list) = List.length rules);
    filtered_list
  let string_of_rule_idx s i = string_of_reference (reference_of_label (Map.find_exn s.label_of_rule i))

end