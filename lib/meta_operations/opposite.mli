open Common

val op_data_to_string : op_data -> string
val tm : ('a, 'b) tm -> op_data -> ('a, 'b) tm
val sub : ('a, 'b) sub -> op_data -> ('a, 'b) sub
val ty : ('a, 'b) ty -> op_data -> ('a, 'b) ty
val ctx : ('a, 'b) ctx -> op_data -> ('a, 'b) ctx

module Make (K : KernelS) : sig
  open K

  val coh : Coh.t -> op_data -> Coh.t
  val checked_tm : Tm.t -> op_data -> Tm.t
  val equiv_op_ps : ps -> op_data -> sub_ps
end
