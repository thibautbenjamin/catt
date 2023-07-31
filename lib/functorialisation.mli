open Kernel

val coh : ps -> ty -> Var.t list -> ps * ty
val tm : ctx -> tm -> Var.t list -> ctx * tm
