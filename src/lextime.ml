open Core
open CalendarLib

module Time = struct

  type t = Calendar.t

  let zero = Calendar.make 0 0 0 0 0 0
  let to_string t = "`" ^ (Printer.Calendar.to_string t) ^ "`"
  let of_string = Printer.Calendar.from_string

  let to_float = Calendar.to_unixfloat
  let of_float = Calendar.from_unixfloat
  
end

module Span = struct

  open Calendar.Period
  
  type t = Calendar.Period.t

  type unit = Second | Minute | Hour | Day | Month | Year

  let zero = make 0 0 0 0 0 0

  let equal = Calendar.Period.equal
  
  let to_string t =
    let value_with_unit x u = if x > 0 then string_of_int x ^ " " ^ u else "" in
    let y, m, d, s = ymds t in
    let h, min, sec = s / 3600, (s % 3600) / 60, s % 60 in
    value_with_unit y "y" ^ value_with_unit m "M" ^ value_with_unit d "d"
    ^ value_with_unit h "h" ^ value_with_unit min "m" ^ value_with_unit sec "s"

  let to_int t =
    let y, m, d, s = ymds t in
    (y * 365 + m * 30 + d) * 86400 + s

  let is_zero t = equal zero t

  let seconds = second

  let of_value_with_unit x pos = function
    | "s" -> second x
    | "m" -> minute x
    | "h" -> hour x
    | "d" -> day x
    | "M" -> month x
    | "y" -> year x
    | "" when x = 0 -> second 0
    | "" -> Util.type_error (Printf.sprintf "Time span without unit must be zero") pos
    | s -> Util.type_error (Printf.sprintf "Invalid time span unit %s" s) pos

  let (+) = add

  let comp base_case span span' =
    let y,  m,  d,  s  = ymds span in
    let y', m', d', s' = ymds span' in
    let rec lexico l l' = match l, l' with
      | [],   [] -> base_case
      | h::_, h'::_  when h < h' -> true
      | h::t, h'::t' when h = h' -> lexico t t'
      | _ -> assert false
    in lexico [y; m; d; s] [y'; m'; d'; s']

  let (<=) span span' = comp true span span'
  let (<)  span span' = comp false span span'

end



