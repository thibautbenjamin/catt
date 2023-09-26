open Kernel
open Kernel.Unchecked_types
open Raw_types

val tm : tmR -> tm * meta_ctx
val ty : tyR -> ty * meta_ctx
val ctx : (Var.t * tyR) list -> ctx * meta_ctx
val sub_to_suspended : sub_ps -> sub_ps * meta_ctx
