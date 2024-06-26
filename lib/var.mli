type t =
| Name of string
| New of int
| Db of int (* storing de Bruijn levels for coherences *)

val to_string : t -> string
val make_var : string -> t
val check_equal : t -> t -> unit
val suspend : t -> t
val fresh : unit -> t
