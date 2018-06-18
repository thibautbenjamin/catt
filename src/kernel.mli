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
    | Obj
    | Arr of tm * tm
    | Ty of kTy
  and tm =
    | Var of Var.t
    | Sub of tm * (tm list)
    | Tm of kTm
end

module rec Tm : sig
  type t

  val make : Ctx.t -> Expr.tm -> t * Ty.t
end

and Ty : sig
  type t

  val make : Ctx.t -> Expr.ty ->  t

  val to_string : t -> string
end

and Ctx : sig
  type t

  val make : (Var.t * Expr.ty) list -> t

  val to_string : t -> string
end

type ctx = Ctx.t

type ty = Expr.ty
type tm = Expr.tm

val string_of_ty : ty -> string
val string_of_tm : tm -> string

val init_env : unit
val add_env : Var.t -> ctx -> ty -> unit

(* val mk_ctx : (Var.t * ty) list -> ctx  *)
val mk_tm : ctx -> tm -> tm * ty
val mk_ty : ctx -> ty -> ty
                           
val checkEqual : ctx -> ty -> ty -> unit

val reinit : tm -> tm

val unify : ctx -> ty -> tm -> ((Var.t * ty) * tm option * bool) list -> ((Var.t * ty) * tm option * bool) list

