open Kernel
open Kernel.Unchecked_types

val coh : coh -> (Var.t * int) list -> coh * ps
val tm : ctx -> tm -> (Var.t * int) list -> ctx * tm
