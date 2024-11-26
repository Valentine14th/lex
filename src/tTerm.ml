open Core

type core_t =
  | TVar of string
  | TConst of Dom.t
  | TApp of string * (t list)
  | TUnop of Term.unop * t
  | TBinop of t * Term.binop * t
  | TProj of t * string
  | TRecord of (string * t) list
and t = { trm: core_t; tt: TypeTerm.t; pos: LexingInfo.t }

let rec to_formula_term_core = function
  | TVar v -> Term.Var v
  | TConst d -> Term.Const d
  | TApp (f, trms) -> Term.App (f, List.map trms ~f:to_formula_term)
  | TUnop (o, trm) -> Term.Unop (o, to_formula_term trm)
  | TBinop (trm, o, trm') -> Term.Binop (to_formula_term trm, o, to_formula_term trm')
  | TProj (trm, p) -> Term.Proj (to_formula_term trm, p)
  | TRecord kvs -> Term.Record (List.map ~f:(fun (k, v) -> (k, to_formula_term v)) kvs)

and to_formula_term (t: t): Term.t = Term.make_term (to_formula_term_core t.trm) t.pos

let unvar = function
  | TVar x -> x
  | TConst _ -> raise (Invalid_argument "unvar is undefined for Consts")
  | TApp _ -> raise (Invalid_argument "unvar is undefined for Apps")
  | TUnop _ -> raise (Invalid_argument "unvar is undefined for Unops")
  | TBinop _ -> raise (Invalid_argument "unvar is undefined for Binops")
  | TProj _ -> raise (Invalid_argument "unvar is undefined for Projs")
  | TRecord _ -> raise (Invalid_argument "unvar is undefined for Records")

let is_const = function
  | TConst _ -> true
  | _ -> false

let unconst = function
  | TVar _ -> raise (Invalid_argument "unconst is undefined for Vars")
  | TConst c -> c
  | TApp _ -> raise (Invalid_argument "unconst is undefined for Apps")
  | TUnop _ -> raise (Invalid_argument "unconst is undefined for Unops")
  | TBinop _ -> raise (Invalid_argument "unconst is undefined for Binops")
  | TProj _ -> raise (Invalid_argument "unconst is undefined for Projs")
  | TRecord _ -> raise (Invalid_argument "unconst is undefined for Records")

let rec fv_list_core = function
  | [] -> []
  | (TVar x, positions) :: trms -> (x, positions) :: fv_list_core trms
  | _ :: trms -> fv_list_core trms

and fv_list trms = fv_list_core (List.map trms ~f:(fun t -> t.trm, t.pos))

let rec equal_core t t' = match t, t' with
  | TVar x, TVar x' -> String.equal x x'
  | TConst d, TConst d' -> Dom.equal d d'
  | TApp (f, ts), TApp (f', ts') ->
     String.equal f f' && (match List.map2 ts ts' ~f:equal with
                           | Ok e -> List.for_all e ~f:(fun x -> x)
                           | Unequal_lengths -> false)
  | TUnop (o, t), TUnop (o', t') -> Term.equal_unop o o' && equal t t'
  | TBinop (t1, o, t2), TBinop (t1', o', t2') ->
     equal t1 t1' && Term.equal_binop o o' && equal t2 t2'
  | _ -> false

and equal t t' = equal_core t.trm t'.trm && TypeTerm.equal t.tt t'.tt

let rec to_string_core = function
  | TVar x -> Printf.sprintf "TVar %s" x
  | TConst d -> Printf.sprintf "TConst %s" (Dom.to_string d)
  | TApp (f, ts) -> Printf.sprintf "TApp %s(%s)" f
                      (String.concat ~sep:", " (List.map ts ~f:to_string))
  | TUnop (o, t) -> Printf.sprintf "TUnop %s (%s)" (Term.string_of_unop o) (to_string t)
  | TBinop (t, o, t') -> Printf.sprintf "TBinop (%s) %s (%s)"
                           (to_string t) (Term.string_of_binop o) (to_string t')
  | TProj (t, p) -> Printf.sprintf "Proj (%s).%s" (to_string t) p
  | TRecord kvs ->
     Printf.sprintf "Record { %s }"
       (String.concat ~sep:", " (List.map kvs ~f:(fun (k, v) -> k ^ " : " ^ to_string v)))


and to_string t = Printf.sprintf "%s : %s" (to_string_core t.trm) (TypeTerm.to_string t.tt)

let rec value_to_string_core ?(l=0) = function
  | TVar x -> Printf.sprintf "%s" x
  | TConst d -> Printf.sprintf "%s" (Dom.to_string d)
  | TApp (f, trms) -> Printf.sprintf "%s(%s)" f (list_to_string trms)
  | TUnop (o, t) -> Printf.sprintf (Util.paren l 10 "%s %s")
                      (Term.string_of_unop o)
                      (value_to_string ~l:10 t)
  | TBinop (t, o, t') -> let l' = Term.prio_of_binop o in
                         Printf.sprintf (Util.paren l l' "%s %s %s")
                           (value_to_string ~l:l' t)
                           (Term.string_of_binop o)
                           (value_to_string ~l:l' t')
  | TProj (t, p) -> Printf.sprintf "%s.%s" (value_to_string ~l:10 t) p
  | TRecord kvs ->
     let f (k, v) = k ^ " : " ^ value_to_string v in
     Printf.sprintf "{ %s }" (String.concat ~sep:", " (List.map kvs ~f))

and list_to_string trms = String.concat ~sep:", " (List.map trms ~f:value_to_string)

and value_to_string ?(l=0) t = 
  Printf.sprintf (Util.paren l 0 "%a : %s")
    (fun _ -> value_to_string_core ~l:5) t.trm (TypeTerm.value_to_string t.tt)

let rec untyped_value_to_string_core ?(l=0) = function
  | TVar x -> Printf.sprintf "%s" x
  | TConst d -> Printf.sprintf "%s" (Dom.to_string d)
  | TApp (f, trms) -> Printf.sprintf "%s(%s)" f (untyped_list_to_string trms)
  | TUnop (o, t) -> Printf.sprintf (Util.paren l 10 "%s %s")
                      (Term.string_of_unop o)
                      (untyped_value_to_string ~l:10 t)
  | TBinop (t, o, t') -> let l' = Term.prio_of_binop o in
                         Printf.sprintf (Util.paren l l' "%s %s %s")
                           (untyped_value_to_string ~l:l' t)
                           (Term.string_of_binop o)
                           (untyped_value_to_string ~l:l' t')
  | TProj (t, p) -> Printf.sprintf "%s.%s" (untyped_value_to_string ~l:10 t) p
  | TRecord kvs ->
     let f (k, v) = k ^ " : " ^ untyped_value_to_string v in
     Printf.sprintf "{ %s }" (String.concat ~sep:", " (List.map kvs ~f))

and untyped_list_to_string trms = String.concat ~sep:", " (List.map trms ~f:untyped_value_to_string)

and untyped_value_to_string ?(l=0) t = 
  Printf.sprintf (Util.paren l 0 "%a") (fun _ -> untyped_value_to_string_core ~l:5) t.trm
