open Kernel
open Kernel.Unchecked_types

val coh : ps -> ty -> Var.t list -> coh
val tm : ctx -> tm -> Var.t list -> ctx * tm
