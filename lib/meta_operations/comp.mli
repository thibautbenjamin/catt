open Common
open Raw_types

module Make (Theory : Theory.S) : sig
  open Kernel.Make(Theory)

  val tree : int -> ps
  val x : int -> constr
  val f : int -> constr
  val comp_n : int -> Coh.t
  val comp : subR -> bool -> Coh.t
  val arity_comp : subR -> bool -> int
  val bcomp : tm -> tm -> tm -> tm -> tm -> tm
end
