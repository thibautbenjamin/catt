open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val coh_depth1 : (Coh.t -> (Var.t list) -> tm * ctx) ref

val preimage : ctx -> sub_ps -> (Var.t list) -> (Var.t list)
val tgt_subst : (Var.t list) -> sub

val coh : Coh.t -> Var.t list -> tm * ctx
val coh_successively : Coh.t -> (Var.t * int) list -> tm * ctx
val coh_depth0 : Coh.t -> Var.t list -> Coh.t
val coh_all : Coh.t -> Coh.t
val tm_one_step_tm : tm -> Var.t list -> tm
val ty : ty -> Var.t list -> tm -> ty
val ctx : ctx -> Var.t list -> ctx
val sub_ps : sub_ps -> Var.t list -> sub_ps
val tm : ctx -> tm -> (Var.t * int) list -> tm * ctx
val ps : ps -> Var.t list ->  ps * (Var.t * int) list
val sub : sub -> Var.t list -> sub
val sub_w_tgt : ps -> sub_ps -> Var.t list -> sub_ps * ps * (Var.t * int) list * Var.t list

val whisk_sub_ps : int -> tm -> ty -> tm -> ty -> sub_ps
