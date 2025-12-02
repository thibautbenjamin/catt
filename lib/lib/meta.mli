open Common

val new_ty : unit -> ('a, 'b) pty
val new_tm : unit -> ('a, 'b) ptm * (int * ('a, 'b) pty)
