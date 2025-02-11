val parse : string -> (Command.prog, unit) result
val parse_file : string -> (Command.prog, unit) result
val init : unit -> unit
val exec : string -> (unit -> unit) -> unit
val loop : unit -> unit
val reset : unit -> unit
