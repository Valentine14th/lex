open Core

let debug = ref true (* TODO: set to false if not needed *)
let debug_print ?(f_name=None) msg =
  if !debug then
    match f_name with
    | Some f_name -> Printf.printf "[DEBUG] %s: %s\n" f_name msg
    | None -> Printf.printf "[DEBUG]: %s\n" msg

type error_type =
  | LexerError
  | ParserError
  | ImportError
  | TypeError
  | LabelError
  | EnforceabilityError
  | ReferenceError
  | CompilerError

let error_type_to_string = function
  | LexerError -> "Lexer error"
  | ParserError -> "Parser error"
  | ImportError -> "Import error"
  | TypeError -> "Type error"
  | LabelError -> "Label error"
  | EnforceabilityError -> "Enforceability error"
  | ReferenceError -> "Reference error"
  | CompilerError -> "Compiler error"

type error = { error_type: error_type;
               error_msg : string;
               error_pos : LexingInfo.t }

let to_string (err: error) : string =
  Printf.sprintf "%s at %s: %s\n"
    (error_type_to_string err.error_type)
    (LexingInfo.to_string err.error_pos)
    err.error_msg

let to_string_multiple (errs: error list) : string =
  String.concat ~sep:"\n" (List.map ~f:to_string errs) 

let warn (msg : string) (pos_opt: LexingInfo.t option) =
  match pos_opt with
  | Some pos ->
     Printf.printf "Warning at %s: %s\n"
       (LexingInfo.to_string pos)
       msg
  | None ->
     Printf.printf "Warning: %s\n" msg

let make error_type error_msg error_pos =
  { error_type; error_msg; error_pos }

let lexer_error = make LexerError
let parser_error = make ParserError
let import_error = make ImportError
let type_error = make TypeError
let label_error = make LabelError
let enforceability_error = make EnforceabilityError
let reference_error = make ReferenceError
let compiler_error = make CompilerError

let fatal error =
  failwith ("Fatal: " ^ to_string error)

module WithErrors = struct

  type 'a t = Ok of 'a | Errors of 'a * error list

  let ok a = Ok a
  let errors a errs = Errors (a, errs)
  let error a err = errors a [err]

  let with_error a err = Errors (a, [err])

  let (>>=) (a: 'a t) (f: 'a -> 'b t) : 'b t =
    match a with
    | Ok a -> f a
    | Errors (a, errs) ->
       match f a with
       | Ok b -> Errors (b, errs)
       | Errors (b, errs') -> Errors (b, errs @ errs')

  let (>|) (a: 'a t) (f: 'a -> 'b) : 'b t =
    match a with
    | Ok a -> Ok (f a)
    | Errors (a, errs) -> Errors (f a, errs)

  let fold ~init:(init:'a) ~f:(f:'a -> 'b -> 'a t) (l: 'b list) : 'a t =
    List.fold ~init:(Ok init) ~f:(fun (a: 'a t) (b: 'b) -> a >>= (fun a -> f a b)) l

  let all (l: 'a t list) : 'a list t =
    let errs, l =
      List.fold_map l ~init:[]
        ~f:(fun errs a ->
          match a with
          | Ok a -> errs, a 
          | Errors (a, errs') -> errs @ errs', a) in
    match errs with
    | [] -> Ok l
    | _  -> Errors (l, errs)

  let (let* ) = (>>=)
  
end

module OrErrors = struct

  type 'a t = Ok of 'a | Errors of error list

  let ok a = Ok a
  let errors errs = Errors errs
  let error err = errors [err]

  let value ~default = function
    | Ok a -> a
    | Errors _ -> default

  let (>>=) (a: 'a t) (f: 'a -> 'b t) : 'b t =
    match a with
    | Ok a -> f a
    | Errors errs -> errors errs

  let (let* ) = (>>=)

  let (>|) (a: 'a t) (f: 'a -> 'b) : 'b t =
    match a with
    | Ok a -> Ok (f a)
    | Errors errs -> Errors errs

  let map2 (a: 'a t) (b: 'b t) (f: 'a -> 'b -> 'c) : 'c t =
    match a, b with
    | Ok a, Ok l -> Ok (f a l)
    | Ok _, Errors errs -> Errors errs
    | Errors errs, Ok _ -> Errors errs
    | Errors errs, Errors errs' -> Errors (errs @ errs')

  let all (l: 'a t list) : 'a list t =
    List.fold_right ~init:(Ok []) ~f:(fun a l -> map2 a l List.cons) l

  let fold ~init:(init:'a) ~f:(f:'a -> 'b -> 'a t) (l: 'b list) : 'a t =
    List.fold ~init:(Ok init) ~f:(fun (a: 'a t) (b: 'b) -> a >>= (fun a -> f a b)) l

  let fold_map ~init:(init:'a) ~f:(f:'a -> 'b -> ('a * 'c) t) (l: 'b list) : ('a * 'c list) t =
    let f (a, acc) b = let* (a, h) = f a b in ok ((a:'a), h::acc) in
    let* a, acc = fold ~init:(init, []) ~f l in
    ok (a, List.rev acc)

  let fold_map_best_effort ~init:(init:'a) ~f:(f:'a -> 'b -> ('a * 'c) t) (l: 'b list) : 'a * 'c t list =
    let f a b = let r = f a b in (value ~default:a (r >| fst), r >| snd) in
    List.fold_map ~init ~f l

  let fold_best_effort ~init:(init:'a) ~f:(f:'a -> 'b -> 'a t) (l: 'b list) : 'a t =
    let a, l = fold_map_best_effort ~init ~f:(fun a b -> f a b >>= (fun a -> ok (a, ()))) l in
    match all l with
    | Ok _ -> ok a
    | Errors errs -> errors errs

  let fold2 ~init:(init:'a) ~f:(f:'a -> 'b -> 'c -> 'a t) (l: 'b list) (l': 'c list) =
    match List.fold2 ~init:(Ok init) ~f:(fun (a: 'a t) (b: 'b) (c: 'c) -> a >>= (fun a -> f a b c)) l l' with
    | Base.List.Or_unequal_lengths.Ok l -> l >| (fun x -> Base.List.Or_unequal_lengths.Ok x)
    | Base.List.Or_unequal_lengths.Unequal_lengths -> Ok (Base.List.Or_unequal_lengths.Unequal_lengths)

  let fold_right ~init:(init:'a) ~f:(f:'b -> 'a -> 'a t) (l: 'b list) : 'a t =
    List.fold_right ~init:(Ok init) ~f:(fun (b: 'b) (a: 'a t) -> a >>= (f b)) l

  let bind2 (a: 'a t) (b: 'b t) (f: 'a -> 'b -> 'c t) : 'c t =
    match a, b with
    | Ok a, Ok l -> f a l
    | Ok _, Errors errs -> Errors errs
    | Errors errs, Ok _ -> Errors errs
    | Errors errs, Errors errs' -> Errors (errs @ errs')

  let combine2 t x y f g h =
    let r = f t x in
    let t = value ~default:t (r >| fst) in
    let s = g t y in
    bind2 (r >| snd) s (fun x' (t, y') -> h t x' y')

  let witherror ~default:(default:'a) (a:'a t) : 'a WithErrors.t =
    match a with
    | Ok a -> WithErrors.Ok a
    | Errors errs -> WithErrors.Errors (default, errs)

  let of_witherror (a:'a WithErrors.t) : 'a t =
    match a with
    | Ok a -> Ok a
    | Errors (_, errs) -> Errors errs

end

  
