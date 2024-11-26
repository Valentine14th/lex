open Core

type unop =
  | USub
  | UNot [@@deriving compare, sexp_of, hash, equal]

let string_of_unop = function
  | USub -> "-"
  | UNot -> "!"

type binop =
  | BAdd | BSub | BMul | BDiv | BPow
  | BAnd | BOr | BXor
  | BEq | BNeq | BLt | BLeq | BGt | BGeq  [@@deriving compare, sexp_of, hash, equal]

let string_of_binop = function
  | BAdd -> "+"
  | BSub -> "-"
  | BMul -> "*"
  | BDiv -> "/"
  | BPow -> "^"
  | BAnd -> "and"
  | BOr  -> "or"
  | BXor -> "xor"
  | BEq  -> "="
  | BNeq -> "<>"
  | BLt  -> "<"
  | BLeq -> "<="
  | BGt  -> ">"
  | BGeq -> ">="

let prio_of_binop = function
  | BXor | BOr -> 1
  | BAnd -> 2
  | BEq | BNeq | BLt | BLeq | BGt | BGeq -> 3
  | BAdd | BSub -> 4
  | BMul | BDiv -> 5
  | BPow -> 6

type core_t =
  | Var of string
  | Const of Dom.t
  | App of string * (t list)
  | Unop of unop * t
  | Binop of t * binop * t
  | Proj of t * string
  | Record of (string * t) list
and t = {trm: core_t; pos: LexingInfo.t} 

let make_term trm pos = {trm; pos}

let var pos x = make_term (Var x) pos
let const pos d = make_term (Const d) pos
let app pos f ts = make_term (App (f, ts)) pos
let unop pos o t = make_term (Unop (o, t)) pos
let binop pos t1 o t2 = make_term (Binop (t1, o, t2)) pos
let proj pos t p = make_term (Proj (t, p)) pos
let record pos kvs = make_term (Record kvs) pos

let unvar t = match t.trm with
  | Var x -> x
  | Const _ -> raise (Invalid_argument "unvar is undefined for Consts")
  | App _ -> raise (Invalid_argument "unvar is undefined for Apps")
  | Unop _ -> raise (Invalid_argument "unvar is undefined for Unops")
  | Binop _ -> raise (Invalid_argument "unvar is undefined for Binops")
  | Proj _ -> raise (Invalid_argument "unvar is undefined for Projs")
  | Record _ -> raise (Invalid_argument "unvar is undefined for Records")

let is_const t = match t.trm with
  | Const _ -> true
  | _ -> false

let unconst t = match t.trm with
  | Var _ -> raise (Invalid_argument "unconst is undefined for Vars")
  | Const c -> c
  | App _ -> raise (Invalid_argument "unconst is undefined for Apps")
  | Unop _ -> raise (Invalid_argument "unconst is undefined for Unops")
  | Binop _ -> raise (Invalid_argument "unconst is undefined for Binops")
  | Proj _ -> raise (Invalid_argument "unconst is undefined for Projs")
  | Record _ -> raise (Invalid_argument "unconst is undefined for Records")

let fv t = match t.trm with
  | Var x -> [x]
  | _ -> []

let fv_list ts = List.concat_map ts ~f:fv

let rec equal t t' = match t.trm, t'.trm with
  | Var x, Var x' -> String.equal x x'
  | Const d, Const d' -> Dom.equal d d'
  | App (f, ts), App (f', ts') ->
     String.equal f f' && (match List.map2 ts ts' ~f:equal with
                           | Ok e -> List.for_all e ~f:(fun x -> x)
                           | Unequal_lengths -> false)
  | Unop (o, t), Unop (o', t') -> equal_unop o o' && equal t t'
  | Binop (t1, o, t2), Binop (t1', o', t2') ->
     equal t1 t1' && equal_binop o o' && equal t2 t2'
  | Proj (t, p), Proj (t', p') ->
     equal t t' && String.equal p p'
  | Record kvs, Record kvs' ->
     let f (k, v) (k', v') = String.equal k k' && equal v v' in
     List.length kvs = List.length kvs' && List.for_all2_exn kvs kvs' ~f
  | _ -> false

let rec to_string t = match t.trm with
  | Var x -> Printf.sprintf "Var %s" x
  | Const d -> Printf.sprintf "Const %s" (Dom.to_string d)
  | App (f, ts) -> Printf.sprintf "App %s(%s)" f
                     (String.concat ~sep:", " (List.map ts ~f:to_string))
  | Unop (o, t) -> Printf.sprintf "Unop %s (%s)" (string_of_unop o) (to_string t)
  | Binop (t, o, t') -> Printf.sprintf "Binop (%s) %s (%s)"
                          (to_string t) (string_of_binop o) (to_string t')
  | Proj (t, p) -> Printf.sprintf "Proj (%s).%s" (to_string t) p
  | Record kvs ->
     Printf.sprintf "Record { %s }"
       (String.concat ~sep:", " (List.map kvs ~f:(fun (k, v) -> k ^ " : " ^ to_string v)))

let rec value_to_string ?(l=0) t = match t.trm with
  | Var x -> Printf.sprintf "%s" x
  | Const d -> Printf.sprintf "%s" (Dom.to_string d)
  | App (f, ts) -> Printf.sprintf "%s(%s)" f
                     (String.concat ~sep:", " (List.map ts ~f:to_string))
  | Unop (o, t) -> Printf.sprintf (Util.paren l 10 "%s %s")
                     (string_of_unop o)
                     (value_to_string ~l:10 t)
  | Binop (t, o, t') -> let l' = prio_of_binop o in
                        Printf.sprintf (Util.paren l l' "%s %s %s")
                          (value_to_string ~l:l' t)
                          (string_of_binop o)
                          (value_to_string ~l:l' t')
  | Proj (t, p) -> Printf.sprintf "%s.%s" (value_to_string ~l:10 t) p
  | Record kvs ->
     let f (k, v) = k ^ " : " ^ value_to_string v in
     Printf.sprintf "{ %s }" (String.concat ~sep:", " (List.map kvs ~f))

let list_to_string trms = String.concat ~sep:", " (List.map trms ~f:value_to_string)
