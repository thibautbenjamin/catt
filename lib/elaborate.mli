open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)
open Raw_types

val ctx : (Var.t * tyR) list -> ctx
val ty : (Var.t * tyR) list -> tyR -> ctx * ty
val tm : (Var.t * tyR) list -> tmR -> ctx * tm
val ty_in_ps : (Var.t * tyR) list -> tyR -> ps * ty
