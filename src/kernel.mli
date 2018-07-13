type kTy
type kTm
type env


module Var : sig
  type t

  val make : string -> t

  val to_string : t -> string
end

module Expr : sig
  type ty =
    | Letin_ty of Var.t * tm * ty
    | Obj
    | Arr of tm * tm
   and tm =
    | Letin_tm of Var.t * tm * tm
    | Var of Var.t
    | Sub of tm * (tm list)
end

type ty = Expr.ty
type tm = Expr.tm

val string_of_ty : ty -> string
val string_of_tm : tm -> string

val init_env : unit -> unit
val add_coh_env : Var.t -> (Var.t * ty) list -> ty -> unit
val add_let_env : Var.t -> (Var.t * ty) list -> tm -> string
val add_let_env_of_ty : Var.t -> (Var.t * ty) list -> tm -> ty -> string

val mk_tm : (Var.t * ty) list -> tm -> string * string
val mk_tm_of_ty : (Var.t * ty) list -> tm -> ty -> unit




