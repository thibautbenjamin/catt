open Common

module Make (Theory : Theory.S) : sig
  open Kernel.Make(Theory)

  val ps : int option -> ps -> ps
  val ty : int option -> ty -> ty
  val tm : int option -> tm -> tm
  val sub_ps : int option -> sub_ps -> sub_ps
  val sub : int option -> sub -> sub
  val ctx : int option -> ctx -> ctx
  val coh : int option -> Coh.t -> Coh.t
  val checked_tm : int option -> Tm.t -> Tm.t
end
