open Common
open Unchecked_types

module Equality (Coh : sig
  type t
end) (Tm : sig
  type t
end) : sig
  open Unchecked_types(Coh)(Tm)

  module Make (_ : sig
    val forget : Coh.t -> ps * Unchecked_types(Coh)(Tm).ty * pp_data
    val to_string : ?unroll:bool -> Coh.t -> string
    val func_data : Coh.t -> (Var.t * int) list list
    val is_equal : Coh.t -> Coh.t -> bool
    val check : ps -> ty -> pp_data -> Coh.t
  end) (_ : sig
    val func_data : Tm.t -> (Var.t * int) list list
    val develop : Tm.t -> Unchecked_types(Coh)(Tm).tm
    val name : Tm.t -> string
    val full_name : Tm.t -> string
    val ctx : Tm.t -> ctx
    val is_equal : Tm.t -> Tm.t -> bool

    val apply :
      (Unchecked_types(Coh)(Tm).ctx -> Unchecked_types(Coh)(Tm).ctx) ->
      (Unchecked_types(Coh)(Tm).tm -> Unchecked_types(Coh)(Tm).tm) ->
      (pp_data -> pp_data) ->
      Tm.t ->
      Tm.t * Unchecked_types(Coh)(Tm).sub
  end) : sig
    val check_equal_ctx : ctx -> ctx -> unit
    val check_equal_ps : ps -> ps -> unit
    val check_equal_ty : ty -> ty -> unit
    val check_equal_tm : tm -> tm -> unit
    val check_equal_sub_ps : sub_ps -> sub_ps -> unit
    val is_equal_ctx : ctx -> ctx -> bool
    val is_equal_ps : ps -> ps -> bool
    val is_equal_ty : ty -> ty -> bool
    val is_equal_tm : tm -> tm -> bool
    val is_equal_sub : sub -> sub -> bool
  end
end
