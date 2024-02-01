open Common
open Unchecked_types

module Unchecked (Coh : sig type t end) : sig
  open Unchecked_types (Coh)

  module Make
      (_ : sig
         val forget : Coh.t -> ps * Unchecked_types(Coh).ty * coh_pp_data
         val to_string : Coh.t -> string
         val func_data : Coh.t -> functorialisation_data option
         val check_equal : Coh.t -> Coh.t -> unit
         val check : ps -> ty -> coh_pp_data -> Coh.t
       end) : sig

    type sub_ps_bp = {sub_ps : sub_ps; l : tm; r : tm}

    val ps_to_string : ps -> string
    val ty_to_string : ty -> string
    val tm_to_string : tm -> string
    val sub_ps_to_string : ?func : functorialisation_data -> sub_ps -> string
    val ctx_to_string : ctx -> string
    val sub_to_string : sub -> string
    val meta_ctx_to_string : meta_ctx -> string
    val coh_pp_data_to_string : ?print_func:bool -> coh_pp_data -> string
    val full_name : coh_pp_data -> string

    val check_equal_ctx : ctx -> ctx -> unit
    val check_equal_ps : ps -> ps -> unit
    val check_equal_ty : ty -> ty -> unit

    val two_fresh_vars : ctx -> Var.t * Var.t
    val dim_ctx : ctx -> int
    val dim_ty : ty -> int
    val dim_ps : ps -> int
    val ps_to_ctx : ps -> ctx
    val identity_ps : ps -> sub_ps
    val tm_apply_sub : tm -> sub -> tm
    val ty_apply_sub : ty -> sub -> ty
    val sub_ps_apply_sub : sub_ps -> sub -> sub_ps
    val ty_sub_preimage : ty -> sub -> ty
    val db_levels : ctx -> ctx * (Var.t * int) list * int
    val rename_ty : ty -> (Var.t * int) list -> ty
    val tm_contains_var : tm -> Var.t -> bool
    val tm_contains_vars : tm -> Var.t list -> bool
    val sub_ps_to_sub : sub_ps -> ps -> sub * ctx
    val suspend_ps : ps -> ps
    val suspend_ty : ty -> ty
    val suspend_tm : tm -> tm
    val suspend_ctx : ctx -> ctx
    val suspend_sub_ps : sub_ps -> sub_ps
    val ps_bdry : ps -> ps
    val ps_src : ps -> sub_ps
    val ps_tgt : ps -> sub_ps

    val tm_sub_preimage : tm -> sub -> tm
    val suspwedge_subs_ps : sub_ps list -> ps list -> sub_ps
    val opsuspwedge_subs_ps : sub_ps list -> ps list -> sub_ps
    val canonical_inclusions : ps list -> sub_ps list
    val ty_to_sub_ps : ty -> sub_ps
    val ps_compose : int -> ps -> ps -> ps * sub_ps * sub_ps
    val pullback_up : int -> ps -> ps -> sub_ps -> sub_ps -> sub_ps
    val sub_ps_to_sub_ps_bp : sub_ps -> sub_ps_bp
    val wedge_sub_ps_bp : sub_ps_bp list -> sub_ps
    val list_to_sub : tm list -> ctx -> sub
  end
end
