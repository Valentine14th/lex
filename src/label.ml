open Core
open Lex

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
  let h =  match l.law with
  | h::_ -> [h]
  | [] -> []
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

let qualified_name_of_level_simple xs = String.concat ~sep:"_" (List.map ~f:fst xs)

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
  (string_of_rule_id2 l.rule_id)

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
  type t = ident * int * ident

  let compare l1 l2 = match l1, l2 with
  | (sk1, i1, n1), (sk2, i2, n2) when String.equal sk1 sk2 && i1 = i2 -> String.compare n1 n2
  | (sk1, i1, _), (sk2, i2, _) when String.equal sk1 sk2 -> Int.compare i1 i2
  | (sk1, _, _), (sk2, _, _) -> String.compare sk1 sk2

  let t_of_sexp = Tuple3.t_of_sexp String.t_of_sexp Int.t_of_sexp String.t_of_sexp
  let sexp_of_t = Tuple3.sexp_of_t String.sexp_of_t Int.sexp_of_t String.sexp_of_t

  let t_of_loc = function
  | LSection (sk, n) -> 
    begin match sk with
    | Law i       -> ("law", i, n)
    | Title i     -> ("title", i, n)
    | Chapter i   -> ("chapter", i, n)
    | Section i   -> ("section", i, n)
    | Article i   -> ("article", i, n)
    | Paragraph i -> ("paragraph", i, n)
    | Point i     -> ("point", i, n)
    | Subpoint i  -> ("subpoint", i, n)
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

  type s = 
    {
      label_of_rule: (int, (t*Lexing.position), Int.comparator_witness) Map.t;
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
    | "" -> Util.label_error "An unlabeled rule already exists in this section, consider using labels" pos
    | _ -> Util.label_error ("A rule with the label '" ^ k ^ "' already exists in this section") pos
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
  | Intermediate map -> Map.fold map ~init:[] ~f:(fun ~key:_ ~data:(tree, rm) acc -> collect_rules_in_tree tree @  Map.data rm @ acc)
  | Leaf -> []

  let rec find_article_subtree pos map name =
    let key = ("article", 0, name) in
    match Map.find map key with
    | Some _ -> map
    | None ->
      let extract_maps = function
      | Intermediate m -> Some m
      | Leaf -> None
      in
      let rec aux = function
      | [] -> assert false
      | [m] -> find_article_subtree pos m name
      | m::ms -> begin try find_article_subtree pos m name with _ -> aux ms
      end in
      let subtrees = Map.data map |> List.map ~f:fst |> List.filter_map ~f:extract_maps in
      begin match List.is_empty subtrees with
      | true -> Util.label_error ("Section '" ^ Location.string_of_t key ^ "' was not found") pos
      | false ->  aux subtrees
      end
  
  let rec find_rules_in_tree pos label = function
  (* TODO: recursively search, if information above article is missing *)
  | Intermediate map ->
    let label' = remove_highest_level label in
    let highest = highest_level label in
    let key = Location.t_of_loc highest in
    begin match highest with
    | LNone ->
      collect_rules_in_tree (Intermediate map)
    | LRule _ -> assert false
    | LSection (sk, n) ->
      let map' = begin match sk with
      | Article 0 -> find_article_subtree pos map n
      | _ -> map
      end in
      begin match highest_level label' with
      | LRule r -> begin try [Map.find_exn map' key |> snd |> (fun x -> Map.find_exn x r)]
                   with _ -> Util.label_error ("Rule '" ^ r ^ "' not found in section '" ^ Location.string_of_t key ^ "'") pos end
      | LNone -> let rm = begin try Map.find_exn map' key |> snd
                 with _ -> Util.label_error ("Section '" ^ Location.string_of_t key ^ "' was not found") pos
        end in
        Map.data rm
      | _ -> let tree' = begin try Map.find_exn map' key |> fst
             with _ -> Util.label_error ("Section '" ^ Location.string_of_t key ^ "' was not found") pos end
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

  let string_of_rule_idx s i = string_of_reference (reference_of_label (fst (Map.find_exn s.label_of_rule i)))
  let pos_of_rule_idx s i = snd (Map.find_exn s.label_of_rule i)
  let add_exception idx refs s =
    let rule_idxs = List.concat_map refs ~f:(fun (pos, l, _) -> find_rules_in_tree pos l s.tree) in
    if List.is_empty rule_idxs then Util.warning ("No rules found for exception " ^ string_of_rule_idx s idx);
    { s with exceptions = List.fold rule_idxs ~init:s.exceptions ~f:(fun m r_idx -> Map.add_multi m ~key:r_idx ~data:idx) }

  let add_scope idx refs s =
    let rule_idxs = List.concat_map refs ~f:(fun (pos, l, _) -> find_rules_in_tree pos l s.tree) in
    if List.is_empty rule_idxs then Util.warning ("No rules found for scope " ^ string_of_rule_idx s idx);
    { s with scopes = List.fold rule_idxs ~init:s.scopes ~f:(fun m r_idx -> Map.add_multi m ~key:r_idx ~data:idx) }


  let rules_with_shared_variables s =
    let rec fixpoint m =
      let f0 acc x = Map.find m x
                    |> Option.value ~default:(Set.empty (module Int))
                    |> Set.union acc
      in
      let f1 v = Set.fold v ~init:v ~f:f0 in
      let m' = Map.map m ~f:f1 in
      match Map.equal Set.equal m m' with
      | true -> m'
      | false -> fixpoint m'
    in
    let aux exceptions scopes =
      let f ~key:_ = function
        | `Left l | `Right l -> Some (Set.of_list (module Int) l)
        | `Both (l1, l2) -> Some (Set.of_list (module Int) (l1@l2))
      in
      let scopes_and_exceptions = Map.merge scopes exceptions ~f:f in
      fixpoint scopes_and_exceptions
    in
    let class_map = aux s.exceptions s.scopes in
    let rules = Map.keys s.label_of_rule in
    let f1 x = function
      | Some s -> Set.add s x
      | None -> Set.singleton (module Int) x
    in
    let f2 acc x = Map.update acc x ~f:(f1 x) in
    let full_map = List.fold rules ~init:class_map ~f:f2 in
    let full_list = Map.data full_map in
    let f3 acc' y = Set.inter acc' y in
    let f4 acc' y =
      let acc'' = List.filter_map acc' ~f:(fun z -> if (Set.is_empty (Set.inter y z)) then None else Some (Set.union y z)) in
      List.fold acc'' ~f:Set.union ~init:y
      in
    let f5 acc x =
      match Set.length (List.fold acc ~init:x ~f:f3) with
      | 0 -> x::acc
      | _ -> [f4 acc x]
    in
    let full_list' = List.dedup_and_sort full_list ~compare:(fun a b -> if Set.equal a b then 0 else 1)  in
    let filtered_list = List.filter full_list' ~f:(fun x -> if List.exists full_list ~f:(fun y -> Set.is_subset x ~of_:y && not (Set.equal x y)) then false else true) in
    let filtered_list' = List.fold filtered_list ~init:[] ~f:f5 in
    assert (List.length full_list = List.length rules);
    assert (List.length (List.concat_map filtered_list' ~f:Set.to_list) = List.length rules);
    filtered_list'


end
