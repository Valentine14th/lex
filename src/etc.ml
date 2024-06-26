open Core

let tabs i = String.make (i*4) ' '

let sanitize_string n =
  String.map n ~f:(function ' ' | '[' | ']' | '.' -> '-' | c -> c)

let concat k (k', v) = (k ^ "__" ^ k', v)
