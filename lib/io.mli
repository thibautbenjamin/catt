val print_string_fun : (string -> unit) ref
val print_endline : string -> unit
val read_line_fun : (unit -> string) ref
val read_lin : unit -> string
val debug : ('a, unit, string, unit) format4 -> 'a
val info : ('a, unit, string, unit) format4 -> 'a
val command : ('a, unit, string, unit) format4 -> 'a

exception Error of string
val error : ('a, unit, string, 'b) format4 -> 'a
