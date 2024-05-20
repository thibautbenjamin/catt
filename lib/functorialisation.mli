open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val builtin_ccomp : (int -> tm) ref

val coh : Coh.t -> functorialisation_data -> Coh.t
val coh_all : Coh.t -> Coh.t
val ctx : ctx -> (Var.t list) -> ctx
val tm : ctx -> tm -> functorialisation_data -> ctx * tm

val whisk : int -> int -> int -> Coh.t
val whisk_sub_ps : int -> tm -> ty -> tm -> ty -> sub_ps
