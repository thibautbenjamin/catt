open Kernel
open Unchecked_types.Unchecked_types(Coh)

val new_ty : unit -> ty
val new_tm : unit -> tm * (int * ty)
