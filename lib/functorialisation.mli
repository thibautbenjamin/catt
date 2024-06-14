open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val cubical_comp : (int -> tm) ref
val depth1_interchanger_src : (Coh.t -> (Var.t list) -> tm * ty) ref
val depth1_interchanger_tgt : (Coh.t -> (Var.t list) -> tm * ty) ref
val depth1_bridge_sub : (sub_ps -> sub_ps -> (Var.t list) -> sub_ps) ref

val find_places : ctx -> sub_ps -> (Var.t list) -> (Var.t list)
val tgt_subst : (Var.t list) -> sub

val coh : Coh.t -> functorialisation_data -> Coh.t
val coh_all : Coh.t -> Coh.t
val tm_one_step_tm : tm -> (Var.t list) -> tm
val ty : ty -> (Var.t list) -> tm -> ty
val ctx : ctx -> (Var.t list) -> ctx
val sub : sub_ps -> (Var.t list) -> sub_ps
val tm : ctx -> tm -> functorialisation_data -> ctx * tm

val whisk : int -> int -> int -> Coh.t
val whisk_sub_ps : int -> tm -> ty -> tm -> ty -> sub_ps
