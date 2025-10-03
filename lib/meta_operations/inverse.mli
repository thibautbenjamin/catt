open Kernel

val ty : ty -> ty
val compute_inverse : tm -> tm
val compute_witness : tm -> tm
val inverse : Tm.t -> Tm.t
