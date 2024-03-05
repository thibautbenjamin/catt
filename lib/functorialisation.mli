open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val builtin_comp : (int -> Coh.t) ref
val builtin_whisk : (int -> int -> int -> Coh.t) ref

val coh : Coh.t -> functorialisation_data -> Coh.t
val coh_all : Coh.t -> Coh.t
val tm : ctx -> tm -> functorialisation_data -> ctx * tm
