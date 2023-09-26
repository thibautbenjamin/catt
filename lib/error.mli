exception UnknownId of string
exception ReservedName of string
exception InvalidEntry
exception OptionsError

val fatal : string -> 'a
val untypable : string -> string -> 'a
val not_valid_coherence : string -> string -> 'a
val unsatisfiable_constraints : string -> string -> 'a
val incomplete_constraints : string -> 'a
val wrong_option_argument : expected:string -> string -> string -> 'a
val incompatible_options : string -> string -> 'a
val unknown_option : string -> 'a
val unknown_id : string -> 'a
val functorialisation : string -> string -> 'a
val parsing_error : string -> string -> 'a
