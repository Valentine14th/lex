open Core

open TypeTerm

let events =
  [("ts", (Lex.Event (false, Variable), ["t", TypeConst Dom.TTime], MFOTL_lib.Enftype.obs, Some "the current time"))]

let events_map = Map.of_alist_exn (module String) events

let functions = []
  (*["day", (["t", TypeConst Dom.TTime], TypeConst Dom.TTime, Some "the day of time {t}")]*)

let functions_map = Map.of_alist_exn (module String) functions
