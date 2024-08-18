open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val phase : (int -> int -> (tm*ty) -> (tm*ty) -> (Var.t*Var.t) list -> Var.t -> tm*ty) ref

val cone_ty : tm -> ty -> (Var.t*Var.t) list -> Var.t -> ty
val cone_tm : tm -> (Var.t*Var.t) list -> Var.t -> tm
val cone_tmty : (tm*ty) -> (Var.t*Var.t) list -> Var.t -> (tm*ty)
val cone_ctx : ctx -> ctx * ((Var.t*Var.t) list * Var.t)
val cone_sub : sub -> (Var.t*Var.t) list -> (Var.t*Var.t) list -> Var.t -> Var.t -> sub

val cones_postprocess_fn : ctx -> tm -> ctx*tm
