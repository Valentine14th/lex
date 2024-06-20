(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type tt = TInt | TStr | TFloat | TBool | TTime | TSpan | TMoney of string

type t =
  | Int of Int.t
  | Str of String.t
  | Float of Float.t
  | Bool of Bool.t
  | Time of Lextime.Time.t
  | Span of Lextime.Span.t
  | Money of Money.t

let equal d d' = match d, d' with
  | Int v, Int v' -> Int.equal v v'
  | Str v, Str v' -> String.equal v v'
  | Float v, Float v' -> Float.equal v v'
  | _ -> false

let tt_equal tt tt' = match tt, tt' with
  | TInt, TInt
    | TStr, TStr
    | TFloat, TFloat
    | TBool, TBool
    | TTime, TTime
    | TSpan, TSpan -> true
  | TMoney c, TMoney c' -> String.equal c c'
  | _ -> false

let tt_of_string = function
  | "int" -> TInt
  | "string" -> TStr
  | "float" -> TFloat
  | "bool" -> TBool
  | "time" -> TTime
  | t ->
     if String.starts_with ~prefix:"money " t then
       TMoney (String.sub t 6 (String.length t))
     else
       raise (Invalid_argument (Printf.sprintf "type %s is not supported" t))

let tt_of_domain = function
  | Int _ -> TInt
  | Str _ -> TStr
  | Float _ -> TFloat
  | Bool _ -> TBool
  | Time _ -> TTime
  | Span _ -> TSpan
  | Money m -> TMoney (Money.currency m)

let string_of_tt = function
  | TInt -> "int"
  | TStr -> "string"
  | TFloat -> "float"
  | TBool -> "bool"
  | TTime -> "time"
  | TSpan -> "span"
  | TMoney c -> "money(" ^ c  ^ ")"

let tt_default = function
  | TInt -> Int 0
  | TStr -> Str ""
  | TFloat -> Float 0.0
  | TBool -> Bool false
  | TTime -> Time Lextime.Time.zero
  | TSpan -> Span Lextime.Span.zero
  | TMoney c -> Money Money.(0. $ c)

let to_string = function
  | Int v -> Int.to_string v
  | Str v -> Printf.sprintf "\"%s\"" v
  | Float v -> Float.to_string v
  | Bool v -> Bool.to_string v
  | Time v -> Lextime.Time.to_string v
  | Span v -> Lextime.Span.to_string v
  | Money v -> Money.to_string v
