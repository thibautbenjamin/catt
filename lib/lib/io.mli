val printf : ('a, out_channel, unit) format -> 'a
val eprintf : ('a, out_channel, unit) format -> 'a
val debug : ('a, unit, string, unit) format4 -> 'a
val info : ?v:int -> string Lazy.t -> unit
val command : ('a, unit, string, unit) format4 -> 'a
val error : ('a, unit, string, unit) format4 -> 'a
