exception NotValid
exception NotAlgebraic
exception UnknownId of string
exception NotEqual of string * string
exception DoubledVar of string
exception DoubleDef of string

val print_endline : string -> unit
val read_line_fun : (unit -> string) ref
val read_lin : unit -> string
val debug : ('a, unit, string, unit) format4 -> 'a
val info : ('a, unit, string, unit) format4 -> 'a
val command : ('a, unit, string, unit) format4 -> 'a

exception Error of string
val error : ('a, unit, string, 'b) format4 -> 'a
