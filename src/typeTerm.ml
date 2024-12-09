
open Core
type t =
  | TypeConst of Dom.tt
  | TypeVar   of string
  | TypeSum   of (string * t) list [@@deriving compare, sexp_of, hash, equal]

let rec to_string = function
  | TypeConst tt -> "TypeConst " ^ Dom.tt_to_string tt
  | TypeVar i    -> "TypeVar " ^ i
  | TypeSum kvs  -> let f (k, v) = k ^ " : " ^ to_string v in
                    "TypeSum {" ^ String.concat ~sep:", " (List.map kvs ~f) ^ "}"

let value_to_string = function
  | TypeConst tt -> Dom.tt_to_string tt
  | TypeVar i    -> i
  | TypeSum kvs  -> let f (k, v) = k ^ " : " ^ to_string v in
                    "{" ^ String.concat ~sep:", " (List.map kvs ~f) ^ "}"

let rec eval aliases = function
  | TypeConst tt -> Some (TypeConst tt)
  | TypeVar v    -> fst (Map.find_exn aliases v)
  | TypeSum kvs  -> let f (k, v) = (k, Option.value_exn (eval aliases v)) in
                    Some (TypeSum (List.map kvs ~f))

let eval_default aliases default = function
  | TypeConst tt -> TypeConst tt
  | TypeVar v    ->
     (match fst (Map.find_exn aliases v) with
      | Some tt -> tt
      | None -> default)
  | TypeSum kvs  -> let f (k, v) = (k, Option.value_exn (eval aliases v)) in
                    TypeSum (List.map kvs ~f)

let rec lub t t' aliases =
  match t, t' with
  | TypeConst tt, TypeConst tt' when Dom.equal_tt tt tt' -> Some (TypeConst tt)
  | TypeVar v , TypeVar v' when String.equal v v' -> Some (TypeVar v)
  | TypeSum kvs, TypeSum kvs' ->
     begin
       if (List.length kvs = List.length kvs')
          && (List.for_all2_exn kvs kvs' ~f:(fun kv kv' -> String.equal (fst kv) (fst kv')))
       then
         let f (k, v) (_, v') = Option.map (lub v v' aliases) ~f:(fun v -> (k, v)) in
         (match Option.all (List.map2_exn kvs kvs' ~f) with
          | Some kvs -> Some (TypeSum kvs)
          | None -> None)
       else
         None
     end
  | TypeVar v, tt' ->
     begin
       match fst (Map.find_exn aliases v) with
       | Some tt when equal tt tt' -> Some (TypeVar v)
       | _ -> None
     end
  | tt, TypeVar v' ->
     begin
       match fst (Map.find_exn aliases v') with
       | Some tt' when equal tt' tt -> Some (TypeVar v')
       | _ -> None
     end
  | _, _ -> None

let rec eval_with_doc_string aliases = function
  | TypeConst tt -> (Dom.tt_to_string tt, None) 
  | TypeVar v    -> (v, snd (Map.find_exn aliases v))
  | TypeSum kvs  -> let f (k, v) = k ^ " : " ^ fst (eval_with_doc_string aliases v) in
                    ("{" ^ String.concat ~sep:", " (List.map kvs ~f) ^ "}", None)


