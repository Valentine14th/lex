open Core

include MFOTL_lib.Ctxt.Make(Dom)

let c = ref (-1)
let fresh () = incr c; !c

let fresh_ttt ctxt =
  let fresh_tv = "t" ^ Int.to_string (fresh ()) in
  add_tv fresh_tv ctxt, TVar fresh_tv

type ctype = CNamed of string | CVar of string [@@deriving compare]
 
let ctype_to_string = function
  | CNamed tn -> tn
  | CVar   tv -> "\'" ^ tv

type constr = (ctype * ttt) list list * LexingInfo.t [@@deriving compare]

type ctxt = {
    ctxt   : t;
    constrs: constr list; (* constraints on base types *)
  }

type t = ttt [@@deriving compare, sexp_of, hash, equal]

let ctxt_to_string = to_string
let to_string = ttt_to_string

let rec eval_aliases aliases = function
  | TConst tt  -> Some (TConst tt)
  | TNamed tn  -> Option.bind (fst (Map.find_exn aliases tn)) ~f:(eval_aliases aliases)
  | TVar   tv  -> raise (Invalid_argument ("eval is not defined on TVar " ^ tv))
  | TSum   kvs -> let f (k, v) = (k, Option.value_exn (eval_aliases aliases v)) in
                    Some (TSum (List.map kvs ~f))

let eval_aliases_default aliases default = function
  | TConst tt  -> TConst tt
  | TNamed tn  -> (match fst (Map.find_exn aliases tn) with
                   | Some tt -> tt
                   | None -> default)
  | TVar   tv  -> raise (Invalid_argument ("eval_default is not defined on TVar " ^ tv))
  | TSum   kvs -> let f (k, v) = (k, Option.value_exn (eval_aliases aliases v)) in
                  TSum (List.map kvs ~f)

let rec unalias aliases = function
  | TConst tt  -> TConst tt
  | TNamed tn  -> (match fst (Map.find_exn aliases tn) with
                     | Some tt' -> unalias aliases tt'
                     | None -> TNamed tn)
  | TVar   tv  -> raise (Invalid_argument ("unalias is not defined on TVar " ^ tv))
  | TSum   kvs -> let f (k, v) = (k, unalias aliases v) in
                    TSum (List.map kvs ~f)

let rec eval_with_doc_string aliases  = function
  | TConst tt  -> (Dom.tt_to_string tt, None) 
  | TNamed tn  -> (tn, snd (Map.find_exn aliases tn))
  | TVar   tv  -> raise (Invalid_argument ("eval_with_doc_string is not defined on TVar " ^ tv))
  | TSum   kvs -> let f (k, v) = k ^ " : " ^ fst (eval_with_doc_string aliases v) in
                  ("{" ^ String.concat ~sep:", " (List.map kvs ~f) ^ "}", None)

let empty_ctxt = { ctxt = empty; constrs = [] }

let merge_ctxt ctxt ctxt' =  {
    ctxt    = merge ctxt.ctxt ctxt'.ctxt;
    constrs = List.dedup_and_sort (ctxt.constrs @ ctxt'.constrs) ~compare:compare_constr
  }

let unify_ctxt ttt ttt' c =
  (*Stdio.print_endline (Printf.sprintf "unify_ctxt(%s, %s)" (ttt_to_string ttt) (ttt_to_string ttt'));*)
  let ctxt, ttt = unify ttt ttt' c.ctxt in { c with ctxt }, ttt

let meet_of_subtypes subtypes x y =
  let rec try1 x y =
    match y with
    | _ when equal_ttt x y -> Some x
    | TNamed tn ->
       (match Map.find subtypes tn with
       | Some z -> try1 x z
       | None -> None)
    | _ -> None
  in
  let r = Option.merge (try1 x y) (try1 y x) ~f:(fun a _ -> a) in
  print_endline (Printf.sprintf "meet %s %s = %s" (ttt_to_string x) (ttt_to_string y) (Option.fold r ~f:(fun _ -> ttt_to_string) ~init:"None"));
  r
  
let of_subtypes_ctxt subtypes =
  let meet = meet_of_subtypes subtypes in
  { empty_ctxt with ctxt = of_meet meet }

let of_alist_ctxt ?(subtypes=Map.empty (module String)) l =
  { empty_ctxt with ctxt = of_alist ~meet:(meet_of_subtypes subtypes) l }

let get_ttt_exn_ctxt x c = get_ttt_exn x c.ctxt

let eval_ctxt ttt c = eval ttt c.ctxt

let to_string_constrs constrs =
  let f = function
    | (CNamed tn, ttt) -> Printf.sprintf "%s : %s"   tn (to_string ttt)
    | (CVar   tv, ttt) -> Printf.sprintf "\'%s : %s" tv (to_string ttt) in
  let f cs = "[" ^ String.concat ~sep:", " (List.map ~f cs) ^ "]" in
  let f constr = "[" ^ String.concat ~sep:", " (List.map ~f constr) ^ "]" in
  let f (constr, pos) = Printf.sprintf "(%s)@%s" (f constr) (LexingInfo.to_string pos) in
  Printf.sprintf "[%s]" (String.concat ~sep:", " (List.map ~f constrs))
  
let to_string_ctxt c =
  Printf.sprintf "{ ctxt = %s;\n   constrs = %s }"
    (ctxt_to_string c.ctxt) (to_string_constrs c.constrs)

let constrain_base_type_ctxt (c: ctxt) (pos: LexingInfo.t) (new_constr: (ttt * tt) list list) =
  let ctxt_err ttt tt =
      raise (CtxtError (
                 Printf.sprintf "type clash: found %s, expected base type %s"
                   (ttt_to_string ttt) (Dom.tt_to_string tt))) in
  let f (ttt, tt') = match ttt with
    | TNamed tn -> Some (CNamed tn, TConst tt')
    | TVar tn -> Some (CVar tn, TConst tt')
    | _ -> ctxt_err ttt tt' in
  let new_constr = List.map ~f:(List.filter_map ~f) new_constr in
  { c with constrs = (new_constr, pos) :: c.constrs }

let constrain_fields_type_ctxt (c: ctxt) (pos: LexingInfo.t) (new_constr: (ttt * bool * (string * ttt) list)) =
  let (ttt, force_all_fields, fields) = new_constr in
  let ctxt_err () =
    raise (CtxtError (
               Printf.sprintf "type clash: found %s, expected fields %s%s"
                 (ttt_to_string ttt)
                 (String.concat ~sep:", "
                    (List.map fields ~f:(fun (f, ttt) -> f ^ " : " ^ to_string ttt)))
                 (if force_all_fields then "..." else ""))) in
  let f ctype =
    [[ctype, 
      if force_all_fields then TSum fields else TSum (("*", TConst Dom.TBool) :: fields)
    ]] in
  let ctxt, new_constrs = match ttt with
    | TNamed tn  -> c.ctxt, [f (CNamed tn)]
    | TVar   tv  -> c.ctxt, [f (CVar tv)]
    | TSum   kvs ->
       if force_all_fields then
         let f ctxt (f, ttt) (k, v) =
           if String.equal f k then fst (unify ttt v ctxt) else ctxt_err () in
         (match List.fold2 fields kvs ~init:c.ctxt ~f with
          | List.Or_unequal_lengths.Ok ctxt -> ctxt, []
          | Unequal_lengths -> ctxt_err())
       else
         let f ctxt (f, ttt) =
           match List.find kvs ~f:(fun (k, _) -> String.equal f k) with
           | Some (_, v) -> fst (unify ttt v ctxt)
           | None -> ctxt_err () in
         List.fold fields ~init:c.ctxt ~f, []
    | _ -> ctxt_err () in
  { ctxt; constrs = (List.map ~f:(fun constr -> (constr, pos)) new_constrs) @ c.constrs }

let check_constrain (aliases: (string, ttt option * 'a, String.comparator_witness) Map.t) (c: ctxt) (constr: (ctype * ttt) list list) =
  let f (ct, b) =
    (*print_endline (Printf.sprintf "check_constrain.f: %s" (ctype_to_string ct));*)
    let ttt = match ct with
      | CNamed tn -> TNamed tn
      | CVar   tv -> eval (TVar tv) c.ctxt in
    (*print_endline (Printf.sprintf "check_constrain.f.ttt = %s" (ttt_to_string ttt));*)
    let equal (k, v) (k', v') =
      ignore (unify_ctxt v v' c);
      String.equal k k' in
    let r = match b with
      | TConst tt ->
         let test = Dom.equal_tt tt in
         (match ttt with
          | TNamed tn -> (match Map.find_exn aliases tn with
                          | (Some (TConst tt'), _) -> test tt'
                          | _ -> false) 
          | TConst tt' -> test tt'
          | _ -> false)
      | TSum (("*", TConst Dom.TBool) :: fields) ->
         let test kvs = List.for_all fields ~f:(List.mem kvs ~equal) in
         (match ttt with
          | TNamed tn -> (match Map.find_exn aliases tn with
                          | (Some (TSum kvs), _) -> test kvs
                          | _ -> false)
          | TSum kvs -> test kvs
          | _ -> false)
      | TSum fields ->
         let test kvs =
           match List.for_all2 fields kvs ~f:equal with
           | List.Or_unequal_lengths.Ok b -> b
           | Unequal_lengths -> false in
         (match ttt with
          | TNamed tn -> (match Map.find_exn aliases tn with
                          | (Some (TSum kvs), _) -> test kvs
                          | _ -> false)
          | TSum kvs -> test kvs
          | _ -> false)
      | _ -> false in
    (*print_endline (Printf.sprintf "check_constrain.f(%s, %s) = %b"
                   (ctype_to_string ct) (ttt_to_string b) r);*)
    r in
  let f (ct, b) = try f (ct, b) with _ -> false in
  let f cs = List.for_all cs ~f in
  List.exists constr ~f
      
let concrete_ctxt aliases (c: ctxt) : ctxt =
  let vars = vars c.ctxt in
  let ctxt = List.fold vars ~init:c.ctxt
               ~f:(fun c v -> fst (type_var v (get_concrete_exn v c) c)) in
  (*print_endline "concrete_ctxt.2";*)
  List.iter c.constrs ~f:(
      fun (constr, pos) ->
      if not (check_constrain aliases c constr) then
        raise (CtxtError (Printf.sprintf
                            "Cannot solve constrain at %s: incorrect base type"
                            (LexingInfo.to_string pos)))
    );
  { ctxt; constrs = [] }
  
