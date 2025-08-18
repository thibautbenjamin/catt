open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val coh_depth1 : (Coh.t -> Var.t list -> Tm.t) ref
val preimage : ctx -> sub_ps -> Var.t list -> Var.t list
val tgt_renaming : Var.t list -> (Var.t * tm) list
val coh : Coh.t -> Var.t list -> Tm.t
val coh_successively : Coh.t -> (Var.t * int) list -> Tm.t
val coh_depth0 : Coh.t -> Var.t list -> Coh.t
val coh_all_depth0 : Coh.t -> Coh.t
val coh_all : Coh.t -> Tm.t
val tm_one_step_tm : tm -> Var.t list -> tm
val ty : ty -> Var.t list -> tm -> ty
val tm : Tm.t -> (Var.t * int) list -> Tm.t
val ctx : ctx -> Var.t list -> ctx
val sub_ps : sub_ps -> Var.t list -> sub_ps
val ps : ps -> Var.t list -> ps * (Var.t * (int * bool)) list
val sub : sub -> Var.t list -> sub
val pp_data : Var.t list -> pp_data -> pp_data

val sub_w_tgt :
  ps ->
  sub_ps ->
  Var.t list ->
  sub_ps * ps * (Var.t * (int * bool)) list * Var.t list

val whisk_sub_ps : int -> tm -> ty -> tm -> ty -> sub_ps
val wcomp : tm * ty -> int -> tm * ty -> tm * ty
