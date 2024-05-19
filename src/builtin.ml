open Core

open Formula.TypeTerm

let functions =
  [("time", ([], TypeConst Dom.TTime, Some "the current time"))]

let functions_map = Map.of_alist_exn (module String) functions
