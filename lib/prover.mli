val parse : string -> (Command.prog, unit) result
val init : unit -> unit
val exec : string -> (unit -> unit) -> unit
val loop : unit -> unit
