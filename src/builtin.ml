open Core

open Formula.TypeTerm

let events =
  [("ts", (Lex.Event (false, Variable), [Lexing.dummy_pos, "~return_value", TypeConst Dom.TTime], Lex.TObs, Some "the current time"))]

let events_map = Map.of_alist_exn (module String) events

let functions =
  ["day", (["t", TypeConst Dom.TTime], TypeConst Dom.TTime, Some "the day of time {t}")]

let functions_map = Map.of_alist_exn (module String) functions
