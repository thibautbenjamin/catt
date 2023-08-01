open Kernel
open Kernel.Unchecked_types

val coh : ps -> ty -> Var.t list -> coh * ps
val tm : ctx -> tm -> Var.t list -> ctx * tm
