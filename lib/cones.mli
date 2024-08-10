open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val cone_ty : tm -> ty -> (Var.t*Var.t) list -> tm -> ty
val cone_tm : tm -> (Var.t*Var.t) list -> tm -> tm
val cone_ctx : ctx -> ctx * ((Var.t*Var.t) list * Var.t)
val cone_sub : sub -> (Var.t*Var.t) list -> Var.t -> Var.t -> sub

val cones_postprocess_fn : ctx -> tm -> ctx*tm
