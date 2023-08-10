type functorialisation_data = int list

module Var : sig
  type t =
    | Name of string
    | New of int
    | Db of int

  val to_string : t -> string
  val make_var : string -> t
  val check_equal : t -> t -> unit
  val increase_lv : t -> int -> int -> t
  val suspend : t -> t
end

module rec Unchecked_types : sig
  type coh_pp_data = string * int * functorialisation_data option

  type ps = Br of ps list

  type ty =
    | Meta_ty of int * sub option
    | Obj
    | Arr of ty * tm * tm
  and tm =
    | Var of Var.t
    | Meta_tm of int * sub option
    | Coh of coh * sub_ps
  and coh =
    | Cohdecl of ps * ty * coh_pp_data
    | Cohchecked of Coh.t
  and sub_ps = (tm * bool) list
  and sub = (Var.t * tm) list
  type ctx = (Var.t * (ty * bool)) list
  type meta_ctx = ((int * ty) list)

end

and Coh : sig
  type t
  val forget : t -> Unchecked_types.ps * Unchecked_types.ty * Unchecked_types.coh_pp_data
end

open Unchecked_types

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
end

module Unchecked : sig
  val ps_to_string : ps -> string
  val ty_to_string : ty -> string
  val tm_to_string : tm -> string
  val sub_ps_to_string : ?func : functorialisation_data -> sub_ps -> string
  val ctx_to_string : ctx -> string
  val sub_to_string : sub -> string
  val coh_to_string : Unchecked_types.coh -> string
  val meta_ctx_to_string : meta_ctx -> string
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
  val tm_contains_vars : tm -> Var.t list -> bool
  val sub_ps_to_sub : sub_ps -> ps -> sub * ctx
  val suspend_ps : ps -> ps
  val suspend_ty : ty -> ty
  val suspend_tm : tm -> tm
  val suspend_ctx : ctx -> ctx
  val suspend_sub_ps : sub_ps -> sub_ps
  val check_equal_coh : coh -> coh -> unit
  val coh_data :Unchecked_types.coh -> Unchecked_types.ps * Unchecked_types.ty * Unchecked_types.coh_pp_data
end

val check_term : Ctx.t -> ?ty:ty -> tm -> Tm.t
val check_coh : Unchecked_types.coh -> Coh.t
