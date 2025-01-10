open Common
open Unchecked_types

module Unchecked (Coh : sig
  type t
end) (Tm : sig
  type t
end) : sig
  open Unchecked_types(Coh)(Tm)

  module Make (_ : sig
    val forget : Coh.t -> ps * Unchecked_types(Coh)(Tm).ty * pp_data
    val to_string : Coh.t -> string
    val func_data : Coh.t -> (Var.t * int) list list
    val check_equal : Coh.t -> Coh.t -> unit
    val check : ps -> ty -> pp_data -> Coh.t
  end) (_ : sig
    val name : Tm.t -> string
    val func_data : Tm.t -> (Var.t * int) list list
    val develop : Tm.t -> Unchecked_types(Coh)(Tm).tm

    val apply :
      (Unchecked_types(Coh)(Tm).ctx -> Unchecked_types(Coh)(Tm).ctx) ->
      (Unchecked_types(Coh)(Tm).tm -> Unchecked_types(Coh)(Tm).tm) ->
      (pp_data -> pp_data) ->
      Tm.t ->
      Tm.t * Unchecked_types(Coh)(Tm).sub
  end) : sig
    type sub_ps_bp = { sub_ps : sub_ps; l : tm; r : tm }

    val check_equal_ctx : ctx -> ctx -> unit
    val check_equal_ps : ps -> ps -> unit
    val check_equal_ty : ty -> ty -> unit
    val check_equal_tm : tm -> tm -> unit
    val check_equal_sub_ps : sub_ps -> sub_ps -> unit
    val dim_ctx : ctx -> int
    val dim_ty : ty -> int
    val dim_ps : ps -> int
    val ps_to_ctx : ps -> ctx
    val identity_ps : ps -> sub_ps
    val tm_apply_sub : tm -> sub -> tm
    val ty_apply_sub : ty -> sub -> ty
    val sub_apply_sub : sub -> sub -> sub
    val sub_ps_apply_sub : sub_ps -> sub -> sub_ps
    val ty_apply_sub_ps : ty -> sub_ps -> ty
    val tm_apply_sub_ps : tm -> sub_ps -> tm
    val sub_ps_apply_sub_ps : sub_ps -> sub_ps -> sub_ps
    val ty_rename : ty -> (Var.t * tm) list -> ty
    val tm_rename : tm -> (Var.t * tm) list -> tm
    val sub_ps_rename : sub_ps -> (Var.t * tm) list -> sub_ps
    val ty_sub_preimage : ty -> sub -> ty
    val db_levels : ctx -> ctx * (Var.t * (int * bool)) list * int
    val db_level_sub : ctx -> sub
    val db_level_sub_inv : ctx -> sub
    val rename_ty : ty -> (Var.t * (int * bool)) list -> ty
    val rename_tm : tm -> (Var.t * (int * bool)) list -> tm
    val tm_contains_var : tm -> Var.t -> bool
    val ty_contains_var : ty -> Var.t -> bool
    val tm_contains_vars : tm -> Var.t list -> bool
    val sub_ps_to_sub : sub_ps -> sub
    val sub_to_sub_ps : sub -> sub_ps
    val suspend_pp_data : pp_data -> pp_data
    val suspend_ps : ps -> ps
    val suspend_ty : ty -> ty
    val suspend_tm : tm -> tm
    val suspend_ctx : ctx -> ctx
    val suspend_sub_ps : sub_ps -> sub_ps
    val suspend_sub : sub -> sub
    val ps_bdry : ps -> ps
    val ps_src : ps -> sub_ps
    val ps_tgt : ps -> sub_ps
    val tm_sub_preimage : tm -> sub -> tm
    val suspwedge_subs_ps : sub_ps list -> ps list -> sub_ps
    val opsuspwedge_subs_ps : sub_ps list -> ps list -> sub_ps
    val canonical_inclusions : ps list -> sub_ps list
    val ty_to_sub_ps : ty -> sub_ps
    val coh_to_sub_ps : tm -> sub_ps
    val ps_compose : int -> ps -> ps -> ps * sub_ps * sub_ps
    val pullback_up : int -> ps -> ps -> sub_ps -> sub_ps -> sub_ps
    val sub_ps_to_sub_ps_bp : sub_ps -> sub_ps_bp
    val wedge_sub_ps_bp : sub_ps_bp list -> sub_ps
    val list_to_sub : tm list -> ctx -> sub
    val list_to_db_level_sub : tm list -> (Var.t * tm) list
    val identity : ctx -> sub

    module Display_maps : sig
      val var_apply_sub : Var.t -> sub -> Var.t
      val pullback : ctx -> sub -> ctx -> sub -> ctx * sub
      val glue : sub -> sub -> sub -> ctx -> sub -> sub
      val pp_data_rename : pp_data -> sub -> pp_data
    end
  end
end
