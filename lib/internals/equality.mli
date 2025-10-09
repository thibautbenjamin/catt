module Make (Core : Core.S) : sig
  open Core
  open Common

  val check_equal_ctx : (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx -> unit
  val check_equal_ps : ps -> ps -> unit
  val check_equal_ty : (Coh.t, Tm.t) ty -> (Coh.t, Tm.t) ty -> unit
  val check_equal_tm : (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm -> unit
  val check_equal_sub_ps : (Coh.t, Tm.t) sub_ps -> (Coh.t, Tm.t) sub_ps -> unit
  val is_equal_ctx : (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx -> bool
  val is_equal_ps : ps -> ps -> bool
  val is_equal_ty : (Coh.t, Tm.t) ty -> (Coh.t, Tm.t) ty -> bool
  val is_equal_tm : (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm -> bool
end
