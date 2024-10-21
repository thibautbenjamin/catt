open Common
open Unchecked_types

module rec Coh : sig
  type t

  val forget : t -> ps * Unchecked_types(Coh)(Tm).ty * pp_data
  val check_equal : t -> t -> unit
  val is_inv : t -> bool
  val to_string : t -> string
  val dim : t -> int

  val src : t -> Tm.t
  val tgt : t -> Tm.t

  val check_noninv :
    ps -> Unchecked_types(Coh)(Tm).tm -> Unchecked_types(Coh)(Tm).tm -> pp_data -> t

  val check_inv :
    ps -> Unchecked_types(Coh)(Tm).tm -> Unchecked_types(Coh)(Tm).tm -> pp_data -> t

  val noninv_srctgt :
    t ->
    Unchecked_types(Coh)(Tm).tm * Unchecked_types(Coh)(Tm).tm * Unchecked_types(Coh)(Tm).ty

  val func_data : t -> (Var.t * int) list list
end
and Ty : sig
  type t

  val forget : t -> Unchecked_types(Coh)(Tm).ty
end

and Tm : sig
  type t

  val typ : t -> Ty.t
  val ctx : t -> Unchecked_types(Coh)(Tm).ctx
  val name : t -> string
  val develop : t -> Unchecked_types(Coh)(Tm).tm
  val apply :
    (Unchecked_types(Coh)(Tm).ctx -> Unchecked_types(Coh)(Tm).ctx) ->
    (Unchecked_types(Coh)(Tm).tm -> Unchecked_types(Coh)(Tm).tm) ->
    (pp_data -> pp_data) ->
    t ->
    t
end

open Unchecked_types(Coh)(Tm)

module Ctx : sig
  type t

  val check : ctx -> t
end

module PS : sig
  exception Invalid

  type t

  val mk : Ctx.t -> t
  val forget : t -> ps
end

module Unchecked : sig
  type sub_ps_bp = { sub_ps : sub_ps; l : tm; r : tm }

  val ps_to_string : ps -> string
  val ty_to_string : ty -> string
  val tm_to_string : tm -> string
  val sub_ps_to_string : ?func:(Var.t * int) list list -> sub_ps -> string
  val ctx_to_string : ctx -> string
  val sub_to_string : sub -> string
  val meta_ctx_to_string : meta_ctx -> string
  val pp_data_to_string : ?print_func:bool -> pp_data -> string
  val full_name : pp_data -> string
  val check_equal_ctx : ctx -> ctx -> unit
  val check_equal_ps : ps -> ps -> unit
  val check_equal_ty : ty -> ty -> unit
  val check_equal_tm : tm -> tm -> unit
  val dim_ctx : ctx -> int
  val dim_ty : ty -> int
  val dim_ps : ps -> int
  val ps_to_ctx : ps -> ctx
  val identity_ps : ps -> sub_ps
  val tm_apply_sub : tm -> sub -> tm
  val ty_apply_sub : ty -> sub -> ty
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
  val sub_to_sub_ps : ps -> sub -> sub_ps
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
  val ps_compose : int -> ps -> ps -> ps * sub_ps * sub_ps
  val pullback_up : int -> ps -> ps -> sub_ps -> sub_ps -> sub_ps
  val ty_to_sub_ps : ty -> sub_ps
  val coh_to_sub_ps : tm -> sub_ps
  val sub_ps_to_sub_ps_bp : sub_ps -> sub_ps_bp
  val wedge_sub_ps_bp : sub_ps_bp list -> sub_ps
  val list_to_sub : tm list -> ctx -> sub
  val list_to_db_level_sub : tm list -> (Var.t * tm) list
end

val check_unnamed_term : Ctx.t -> ?ty:ty -> tm -> Tm.t
val check_term : Ctx.t -> pp_data -> ?ty:ty -> tm -> Tm.t
val check_coh : ps -> ty -> pp_data -> Coh.t
