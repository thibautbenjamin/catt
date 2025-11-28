open Common

module Make (C : Core.S) : sig
  open C

  val check_equal_ctx : ctx -> ctx -> unit
  val check_equal_ps : ps -> ps -> unit
  val check_equal_ty : ty -> ty -> unit
  val check_equal_tm : tm -> tm -> unit
  val check_equal_sub_ps : sub_ps -> sub_ps -> unit
  val is_equal_ctx : ctx -> ctx -> bool
  val is_equal_ps : ps -> ps -> bool
  val is_equal_ty : ty -> ty -> bool
  val is_equal_tm : tm -> tm -> bool
end
