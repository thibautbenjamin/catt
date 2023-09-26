open Kernel
open Kernel.Unchecked_types

val coh : ps -> ty -> (Var.t * int) list -> coh * ps
val tm : ctx -> tm -> (Var.t * int) list -> ctx * tm
