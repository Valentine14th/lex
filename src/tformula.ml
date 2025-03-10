
(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Core

module Modules = MFOTL_lib.Modules
module Side = MFOTL_lib.Side

module StringVar = Term.StringVar

type tinfo_type = {
    pos: LexingInfo.t;
    event_type_opt: Lex.event_type option;
    t_vars: (string * TypeTerm.t) list;
  } [@@deriving compare, sexp_of, hash, equal]

module Info : MFOTL_lib.Modules.I with type t = tinfo_type = struct
  
  type t = tinfo_type [@@deriving compare, sexp_of, hash, equal]

  let to_string _ s _ = s
    (* "{ " ^ s ^ "; t_vars = " ^ String.concat ~sep:", " (List.map ~f:(fun (k, v) -> k ^ " -> " ^ TypeTerm.to_string v) info.t_vars) ^ " }"*)
  
  let dummy = { pos = LexingInfo.dummy; event_type_opt = None; t_vars = [] }

end

include MFOTL_lib.MFOTL.Make(Info)(StringVar)(Dom)(TTerm)

module StringMap = Map.Make(String)
