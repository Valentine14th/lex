(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Core

module Time = MFOTL_lib.Time
module Span = MFOTL_lib.Time.Span

type tt =
  | TInt
  | TStr
  | TFloat
  | TBool
  | TTime
  | TSpan
  | TMoney of string [@@deriving compare, sexp_of, hash, equal]

let equal_tt tt tt' =
  match tt, tt' with
  | TMoney "*", TMoney _ -> true
  | TMoney _, TMoney "*" -> true
  | _, _ -> equal_tt tt tt'

type t =
  | Int of Int.t
  | Str of String.t
  | Float of Float.t
  | Bool of Bool.t
  | Time of Time.t
  | Span of Span.s
  | Money of Money.t [@@deriving compare, sexp_of, hash, equal]

let bool_tt = Bool true

(*let tt_of_string = function
  | "int" -> TInt
  | "string" -> TStr
  | "float" -> TFloat
  | "bool" -> TBool
  | "time" -> TTime
  | t ->
     if String.starts_with ~prefix:"money " t then
       TMoney (String.sub t 6 (String.length t))
     else
       raise (Invalid_argument (Printf.sprintf "type %s is not supported" t))*)

let tt_of_domain = function
  | Int _ -> TInt
  | Str _ -> TStr
  | Float _ -> TFloat
  | Bool _ -> TBool
  | Time _ -> TTime
  | Span _ -> TSpan
  | Money m -> TMoney (Money.currency m)

let tt_to_string = function
  | TInt -> "int"
  | TStr -> "string"
  | TFloat -> "float"
  | TBool -> "bool"
  | TTime -> "time"
  | TSpan -> "span"
  | TMoney c -> "money " ^ c

let tt_default = function
  | TInt -> Int 0
  | TStr -> Str ""
  | TFloat -> Float 0.0
  | TBool -> Bool false
  | TTime -> Time Time.zero
  | TSpan -> Span Time.Span.zero
  | TMoney c -> Money Money.(0. $ c)

let to_string = function
  | Int v -> Int.to_string v
  | Str v -> Printf.sprintf "\"%s\"" v
  | Float v -> Float.to_string v
  | Bool v -> Bool.to_string v
  | Time v -> Time.to_string v
  | Span v -> Span.to_string v
  | Money v -> Money.to_string v
     
let to_latex = function
  | Int v -> Int.to_string v
  | Str v -> Printf.sprintf "\\texttt{\"%s\"}" v
  | Float v -> Float.to_string v
  | Bool true -> "\\top"
  | Bool false -> "\\bot"
  | Time v -> Time.to_string v
  | Span v -> Span.to_string v
  | Money v -> Money.to_string v

let of_int i = Int i
