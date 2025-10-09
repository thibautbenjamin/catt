open Common

module rec Coh : sig
  type t

  val forget : t -> ps * (Coh.t, Tm.t) ty * pp_data
  val is_equal : t -> t -> bool
  val check_equal : t -> t -> unit
  val is_inv : t -> bool
  val to_string : ?unroll:bool -> t -> string
  val dim : t -> int
  val src : t -> (Coh.t, Tm.t) tm
  val tgt : t -> (Coh.t, Tm.t) tm
  val check : ps -> (Coh.t, Tm.t) ty -> pp_data -> t
  val check_noninv : ps -> (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm -> pp_data -> t
  val check_inv : ps -> (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm -> pp_data -> t

  val noninv_srctgt :
    t -> (Coh.t, Tm.t) tm * (Coh.t, Tm.t) tm * (Coh.t, Tm.t) ty

  val func_data : t -> (Var.t * int) list list

  val apply_ps :
    (ps -> ps) ->
    ((Coh.t, Tm.t) ty -> (Coh.t, Tm.t) ty) ->
    (pp_data -> pp_data) ->
    t ->
    t

  val apply :
    ((Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx) ->
    ((Coh.t, Tm.t) ty -> (Coh.t, Tm.t) ty) ->
    (pp_data -> pp_data) ->
    t ->
    t * (Coh.t, Tm.t) sub
end

and Ty : sig
  type t

  val forget : t -> (Coh.t, Tm.t) ty
end

and Tm : sig
  type t

  val typ : t -> Ty.t
  val ty : t -> (Coh.t, Tm.t) ty
  val forget : t -> (Coh.t, Tm.t) tm
  val constr : t -> (Coh.t, Tm.t) constr
  val bdry : t -> t * t
  val ctx : t -> (Coh.t, Tm.t) ctx
  val name : t -> string option
  val full_name : t -> string option
  val func_data : t -> (Var.t * int) list list option
  val of_coh : Coh.t -> t
  val develop : t -> (Coh.t, Tm.t) tm
  val pp_data : t -> pp_data option
  val to_string : t -> string
  val is_equal : t -> t -> bool

  val apply :
    ((Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx) ->
    ((Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm) ->
    (pp_data -> pp_data) ->
    t ->
    t * (Coh.t, Tm.t) sub
end

module Core : sig
  module Coh = Coh
  module Tm = Tm
end

include module type of Syntax.Make (Core)

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
