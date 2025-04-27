open Core

let z3_to = ref "0"

let take l n =
  let rec aux = function
    | _, 0 -> []
    | [], _ -> raise (Invalid_argument (string_of_int n))
    | x::xs, i -> x :: aux (xs, (i - 1))
  in
  aux (l, n)

let butlast l = List.take l (List.length l - 1)

let string_of_string_list ?(quotes=true) l =
  if quotes then
    Printf.sprintf "[%s]"
      (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s\"%s\";" acc s))
  else
    Printf.sprintf "[%s]"
      (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%s;" acc s))

let string_of_string_list_new_line ?(prefix="") l = Printf.sprintf "%s"
                            (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%s%s\n" acc prefix s))
let string_of_int_list l = Printf.sprintf "[%s]"
                           (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%d; " acc s))
let string_of_int_to_int_multi_map m = Printf.sprintf "{%s}"
                                       (List.fold (Map.to_alist m) ~init:"" ~f:(fun acc (k, v) -> Printf.sprintf "%s%d -> %s; " acc k (string_of_int_list v)))

let string_of_int_set s = Printf.sprintf "{%s}"
                           (Set.fold s ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%d; " acc s))

let string_of_string_set s = Printf.sprintf "{%s}"
                           (Set.fold s ~init:"" ~f:(fun acc s -> Printf.sprintf "%s\"%s\"; " acc s))

let string_of_int_set_list l = Printf.sprintf "[%s]"
                               (List.fold l ~init:"" ~f:(fun acc s -> Printf.sprintf "%s%s; " acc (string_of_int_set s)))

let spaces i = String.init i ~f:(fun _ -> ' ')
  
let paren h k x = if h>k then "("^^x^^")" else x
let paren_string h k x = if h>=k then "("^x^")" else x

let comb x y =
  match x, y with
  | Some z, _ -> Some z
  | _, Some z -> Some z
  | _, _ -> None

let invert_int_string_multimap (m: (int, string list, _) Map.t) : (string, int list, _) Map.t =
  Map.fold m ~init:(Map.empty (module String)) ~f:(fun ~key:k ~data:v acc ->
      List.fold v ~init:acc ~f:(fun acc s ->
          match Map.find acc s with
          | Some l -> Map.set acc ~key:s ~data:(k::l)
          | None -> Map.set acc ~key:s ~data:[k]))

let remove_at idx lst =
  let rec aux i acc = function
    | [] -> List.rev acc
    | _::tl when i = idx -> List.rev_append acc tl
    | hd::tl -> aux (i + 1) (hd::acc) tl
  in
  aux 0 [] lst

let lists_with_one_removed lst =
  let rec aux i acc =
    if i >= List.length lst then List.rev acc
    else aux (i + 1) ((remove_at i lst)::acc)
  in
  aux 0 []

let combine_string_descriptors (ds: string list) (bs: bool list): string =
  let ds' = List.filteri ds ~f:(fun i _ -> not (List.nth_exn bs i)) in
  let aux = function
    | [] -> ""
    | [d] -> d
    | [d1; d2] -> d1 ^ " and " ^ d2
    | ds -> (String.concat ~sep:", " (butlast ds)) ^ ", and " ^ (List.last_exn ds)
  in
  aux ds'

let string_of_pols ~f (pols: (string, 'enftype, 'string_comp) Map.t): string =
  let aux (k, v) = Printf.sprintf "%s: %s" k (f v) in
  string_of_string_list ~quotes:false (List.map (Map.to_alist pols) ~f:aux)

let string_of_int_string_multimap (m: (int, string list, _) Map.t) : string =
  let aux (k, v) = Printf.sprintf "%d: %s" k (string_of_string_list v) in
  string_of_string_list ~quotes:false (List.map (Map.to_alist m) ~f:aux)

let tabs i = String.make (i*4) ' '

let sanitize_string n =
  String.map n ~f:(function ' ' | '[' | ']' | '.' -> '-' | c -> c)

let concat k (k', v) = ((if String.is_empty k' then k else k ^ "__" ^ k'), v)

let concat_all_filename = function
  | [] -> ""
  | init::idents -> List.fold_left idents ~init ~f:Filename.concat

let intersection_of_int_lists (l1: int list) (l2: int list): int list =
  List.filter l1 ~f:(fun x -> List.mem l2 x ~equal:Int.equal)

let equal_elements_int_lists l1 l2 =
  List.length l1 = List.length l2 && List.for_all l1 ~f:(fun x -> List.mem l2 x ~equal:Int.equal)
