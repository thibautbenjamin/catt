open Common

module Make (_ : Theory.S) : sig
  include KernelS

  val check_term : Ctx.t -> ?ty:ty -> ?name:pp_data -> tm -> Tm.t
  val check_constr : ?name:pp_data -> ctx -> constr -> Tm.t
  val check_coh : ps -> ty -> pp_data -> Coh.t
  val check_sub : ctx -> sub -> ctx -> unit
end
