type t =
| Name of string
| New of int
| Db of int (* storing de Bruijn levels for coherences *)
| Plus of t (* x+ funct. copy of var x *)
| Bridge of t (* x~ funct. var of x *)

val to_string : t -> string
val make_var : string -> t
val check_equal : t -> t -> unit
val suspend : t -> t
val fresh : unit -> t
