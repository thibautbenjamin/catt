open Common

val op_data_to_string : op_data -> string

module Make (K : KernelExt.S) : sig
  open K

  val tm : tm -> op_data -> tm
  val sub : sub -> op_data -> sub
  val ty : ty -> op_data -> ty
  val ctx : ctx -> op_data -> ctx
  val coh : Coh.t -> op_data -> Coh.t
  val checked_tm : Tm.t -> op_data -> Tm.t
  val equiv_op_ps : ps -> op_data -> sub_ps
end
