open Common
open Unchecked_types

module rec Coh : sig
  type t
  val forget : t -> ps * Unchecked_types(Coh).ty * coh_pp_data
  val check_equal : t -> t -> unit
  val to_string : t -> string
  val check_noninv :
    ps -> Unchecked_types(Coh).tm -> Unchecked_types(Coh).tm -> coh_pp_data -> t
  val func_data : t -> functorialisation_data option
end

open Unchecked_types(Coh)
module Ctx : sig
  type t

  val check : ctx -> t
end

module Ty : sig
  type t

  val forget : t -> ty
end

module Tm : sig
  type t

  val typ : t -> Ty.t
end

module PS : sig
  type t

  val mk : Ctx.t -> t
  val forget : t -> ps
  val bdry : int -> t -> t
end

module Unchecked : sig
  val ps_to_string : ps -> string
  val ty_to_string : ty -> string
  val tm_to_string : tm -> string
  val sub_ps_to_string : ?func : functorialisation_data -> sub_ps -> string
  val ctx_to_string : ctx -> string
  val sub_to_string : sub -> string
  val meta_ctx_to_string : meta_ctx -> string
  val coh_pp_data_to_string : ?print_func:bool -> coh_pp_data -> string

  val check_equal_ctx : ctx -> ctx -> unit
  val check_equal_ps : ps -> ps -> unit
  val check_equal_ty : ty -> ty -> unit

  val two_fresh_vars : ctx -> Var.t * Var.t
  val dim_ctx : ctx -> int
  val dim_ty : ty -> int
  val dim_ps : ps -> int
  val ps_to_ctx : ps -> ctx
  val identity_ps : ctx -> sub_ps
  val tm_apply_sub : tm -> sub -> tm
  val ty_apply_sub : ty -> sub -> ty
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

  val tm_sub_preimage : tm -> sub -> tm
end


val check_term : Ctx.t -> ?ty:ty -> tm -> Tm.t
val check_coh : ps -> ty -> coh_pp_data -> Coh.t
