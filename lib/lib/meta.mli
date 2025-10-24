open Common

val new_ty : unit -> ('a, 'b) ty
val new_tm : unit -> ('a, 'b) tm * (int * ('a, 'b) ty)
