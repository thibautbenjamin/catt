module Make (Theory : Theory.S) : sig
  open Kernel.Make(Theory)

  val ty : ty -> ty
  val compute_inverse : tm -> tm
  val compute_witness : tm -> tm
  val inverse : Tm.t -> Tm.t
end
