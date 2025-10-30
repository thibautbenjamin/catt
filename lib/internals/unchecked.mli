module Make (Core : Core.S) : sig
  open Core
  open Common

  type sub_ps_bp = {
    sub_ps : (Coh.t, Tm.t) sub_ps;
    l : (Coh.t, Tm.t) tm;
    r : (Coh.t, Tm.t) tm;
  }

  val dim_ctx : (Coh.t, Tm.t) ctx -> int
  val dim_ty : (Coh.t, Tm.t) ty -> int
  val dim_ps : ps -> int
  val ps_to_ctx : ps -> (Coh.t, Tm.t) ctx
  val identity_ps : ps -> (Coh.t, Tm.t) sub_ps
  val tm_apply_sub : (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) tm
  val ty_apply_sub : (Coh.t, Tm.t) ty -> (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) ty

  val sub_apply_sub :
    (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) sub

  val sub_ps_apply_sub :
    (Coh.t, Tm.t) sub_ps -> (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) sub_ps

  val ty_apply_sub_ps :
    (Coh.t, Tm.t) ty -> (Coh.t, Tm.t) sub_ps -> (Coh.t, Tm.t) ty

  val tm_apply_sub_ps :
    (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) sub_ps -> (Coh.t, Tm.t) tm

  val sub_ps_apply_sub_ps :
    (Coh.t, Tm.t) sub_ps -> (Coh.t, Tm.t) sub_ps -> (Coh.t, Tm.t) sub_ps

  val ty_rename :
    (Coh.t, Tm.t) ty -> (Var.t * (Coh.t, Tm.t) tm) list -> (Coh.t, Tm.t) ty

  val tm_rename :
    (Coh.t, Tm.t) tm -> (Var.t * (Coh.t, Tm.t) tm) list -> (Coh.t, Tm.t) tm

  val sub_ps_rename :
    (Coh.t, Tm.t) sub_ps ->
    (Var.t * (Coh.t, Tm.t) tm) list ->
    (Coh.t, Tm.t) sub_ps

  val ty_sub_preimage :
    (Coh.t, Tm.t) ty -> (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) ty

  val db_levels :
    (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx * (Var.t * (int * bool)) list * int

  val db_level_sub : (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) sub
  val db_level_sub_inv : (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) sub

  val rename_ty :
    (Coh.t, Tm.t) ty -> (Var.t * (int * bool)) list -> (Coh.t, Tm.t) ty

  val rename_tm :
    (Coh.t, Tm.t) tm -> (Var.t * (int * bool)) list -> (Coh.t, Tm.t) tm

  val tm_contains_var : (Coh.t, Tm.t) tm -> Var.t -> bool
  val ty_contains_var : (Coh.t, Tm.t) ty -> Var.t -> bool
  val tm_contains_vars : (Coh.t, Tm.t) tm -> Var.t list -> bool
  val sub_ps_to_sub : (Coh.t, Tm.t) sub_ps -> (Coh.t, Tm.t) sub
  val sub_to_sub_ps : (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) sub_ps
  val suspend_pp_data : pp_data -> pp_data
  val suspend_ps : ps -> ps
  val suspend_ty : (Coh.t, Tm.t) ty -> (Coh.t, Tm.t) ty
  val suspend_tm : (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm
  val suspend_ctx : (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx
  val suspend_sub_ps : (Coh.t, Tm.t) sub_ps -> (Coh.t, Tm.t) sub_ps
  val suspend_sub : (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) sub
  val ps_bdry : ps -> ps
  val ps_src : ps -> (Coh.t, Tm.t) sub_ps
  val ps_tgt : ps -> (Coh.t, Tm.t) sub_ps

  val tm_sub_preimage :
    (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) sub -> (Coh.t, Tm.t) tm

  val suspwedge_subs_ps :
    (Coh.t, Tm.t) sub_ps list -> ps list -> (Coh.t, Tm.t) sub_ps

  val opsuspwedge_subs_ps :
    (Coh.t, Tm.t) sub_ps list -> ps list -> (Coh.t, Tm.t) sub_ps

  val canonical_inclusions : ps list -> (Coh.t, Tm.t) sub_ps list
  val ty_to_sub_ps : (Coh.t, Tm.t) ty -> (Coh.t, Tm.t) sub_ps
  val coh_to_sub_ps : (Coh.t, InnerTm.t) tm -> (Coh.t, InnerTm.t) sub_ps

  val ps_compose :
    int -> ps -> ps -> ps * (Coh.t, Tm.t) sub_ps * (Coh.t, Tm.t) sub_ps

  val pullback_up :
    int ->
    ps ->
    ps ->
    (Coh.t, Tm.t) sub_ps ->
    (Coh.t, Tm.t) sub_ps ->
    (Coh.t, Tm.t) sub_ps

  val sub_ps_to_sub_ps_bp : (Coh.t, Tm.t) sub_ps -> sub_ps_bp
  val wedge_sub_ps_bp : sub_ps_bp list -> (Coh.t, Tm.t) sub_ps

  val list_to_sub :
    (Coh.t, Tm.t) tm list -> (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) sub

  val list_to_db_level_sub :
    (Coh.t, Tm.t) tm list -> (Var.t * (Coh.t, Tm.t) tm) list

  val identity : (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) sub
  val disc : int -> ps
  val disc_ctx : int -> (Coh.t, Tm.t) ctx
  val disc_type : int -> (Coh.t, Tm.t) ty
  val sphere : int -> (Coh.t, Tm.t) ctx
  val sphere_inc : int -> (Coh.t, Tm.t) sub
  val disc_src : int -> (Coh.t, Tm.t) sub_ps
  val disc_tgt : int -> (Coh.t, Tm.t) sub_ps
  val develop_tm : (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm
  val develop_ty : (Coh.t, Tm.t) ty -> (Coh.t, Tm.t) ty
end
