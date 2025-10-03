open Common
open Unchecked_types

module rec Coh : sig
  type t

  val forget : t -> ps * Unchecked_types(Coh)(Tm).ty * pp_data
  val is_equal : t -> t -> bool
  val check_equal : t -> t -> unit
  val is_inv : t -> bool
  val to_string : ?unroll:bool -> t -> string
  val dim : t -> int
  val src : t -> Unchecked_types(Coh)(Tm).tm
  val tgt : t -> Unchecked_types(Coh)(Tm).tm
  val check : ps -> Unchecked_types(Coh)(Tm).ty -> pp_data -> t

  val check_noninv :
    ps ->
    Unchecked_types(Coh)(Tm).tm ->
    Unchecked_types(Coh)(Tm).tm ->
    pp_data ->
    t

  val check_inv :
    ps ->
    Unchecked_types(Coh)(Tm).tm ->
    Unchecked_types(Coh)(Tm).tm ->
    pp_data ->
    t

  val noninv_srctgt :
    t ->
    Unchecked_types(Coh)(Tm).tm
    * Unchecked_types(Coh)(Tm).tm
    * Unchecked_types(Coh)(Tm).ty

  val func_data : t -> (Var.t * int) list list

  val apply_ps :
    (ps -> ps) ->
    (Unchecked_types(Coh)(Tm).ty -> Unchecked_types(Coh)(Tm).ty) ->
    (pp_data -> pp_data) ->
    t ->
    t

  val apply :
    (Unchecked_types(Coh)(Tm).ctx -> Unchecked_types(Coh)(Tm).ctx) ->
    (Unchecked_types(Coh)(Tm).ty -> Unchecked_types(Coh)(Tm).ty) ->
    (pp_data -> pp_data) ->
    t ->
    t * Unchecked_types(Coh)(Tm).sub
end

and Ty : sig
  type t

  val forget : t -> Unchecked_types(Coh)(Tm).ty
end

and Tm : sig
  type t

  val typ : t -> Ty.t
  val ty : t -> Unchecked_types(Coh)(Tm).ty
  val forget : t -> Unchecked_types(Coh)(Tm).tm
  val constr : t -> Unchecked_types(Coh)(Tm).constr
  val bdry : t -> t * t
  val ctx : t -> Unchecked_types(Coh)(Tm).ctx
  val name : t -> string option
  val full_name : t -> string option
  val func_data : t -> (Var.t * int) list list option
  val of_coh : Coh.t -> t
  val develop : t -> Unchecked_types(Coh)(Tm).tm
  val pp_data : t -> pp_data option
  val to_string : t -> string
  val is_equal : t -> t -> bool

  val apply :
    (Unchecked_types(Coh)(Tm).ctx -> Unchecked_types(Coh)(Tm).ctx) ->
    (Unchecked_types(Coh)(Tm).tm -> Unchecked_types(Coh)(Tm).tm) ->
    (pp_data -> pp_data) ->
    t ->
    t * Unchecked_types(Coh)(Tm).sub
end

open Syntax.Syntax(Coh)(Tm)
include module type of Make (Coh) (Tm)

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

val check_term : Ctx.t -> ?ty:ty -> ?name:pp_data -> tm -> Tm.t
val check_constr : ?name:pp_data -> ctx -> constr -> Tm.t
val check_coh : ps -> ty -> pp_data -> Coh.t
val check_sub : ctx -> sub -> ctx -> unit
