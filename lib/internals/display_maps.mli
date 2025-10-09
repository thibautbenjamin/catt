module Make (Core : Core.S) : sig
  open Core
  open Common

  val var_apply_sub : Var.t -> (Coh.t, Tm.t) sub -> Var.t

  val pullback :
    (Coh.t, Tm.t) ctx ->
    (Coh.t, Tm.t) sub ->
    (Coh.t, Tm.t) ctx ->
    (Coh.t, Tm.t) sub ->
    (Coh.t, Tm.t) ctx * (Coh.t, Tm.t) sub

  val glue :
    (Coh.t, Tm.t) sub ->
    (Coh.t, Tm.t) sub ->
    (Coh.t, Tm.t) sub ->
    (Coh.t, Tm.t) ctx ->
    (Coh.t, Tm.t) sub ->
    (Coh.t, Tm.t) sub

  val pp_data_rename : pp_data -> (Coh.t, Tm.t) sub -> pp_data
end
