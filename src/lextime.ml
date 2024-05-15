open Core
open CalendarLib

module Time = struct

  type t = Calendar.t

  let zero = Calendar.make 0 0 0 0 0 0
  let to_string t = "`" ^ (Printer.Calendar.to_string t) ^ "`"
  let of_string = Printer.Calendar.from_string
  
end

module Span = struct

  open Calendar.Period
  
  type t = Calendar.Period.t

  type unit = Second | Minute | Hour | Day | Month | Year

  let zero = make 0 0 0 0 0 0
  
  let to_string t =
    let value_with_unit x u = if x > 0 then string_of_int x ^ " " ^ u else "" in
    let y, m, d, s = ymds t in
    let h, min, sec = s / 3600, (s % 3600) / 60, s % 60 in
    value_with_unit y "y" ^ value_with_unit m "m" ^ value_with_unit d "d"
    ^ value_with_unit h "h" ^ value_with_unit min "min" ^ value_with_unit sec "sec"

  let of_value_with_string_unit x pos = function
    | "s" -> second x
    | "m" -> minute x
    | "h" -> hour x
    | "d" -> day x
    | "M" -> month x
    | "y" -> year x
    | s -> Util.type_error (Printf.sprintf "Invalid time span unit %s" s) pos

  let (+) = add
  
end



