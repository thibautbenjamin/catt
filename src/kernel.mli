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
    | Ty of kTy
   and tm =
    | Letin_tm of Var.t * tm * tm
    | Var of Var.t
    | Sub of tm * (tm list)
    | Tm of kTm
end
                
module Ctx : sig
  type t

  val make : (Var.t * Expr.ty) list -> t
end

type ctx = Ctx.t

type ty = Expr.ty
type tm = Expr.tm

val string_of_ty : ty -> string
val string_of_tm : tm -> string

val init_env : unit -> unit
val add_coh_env : Var.t -> ctx -> ty -> unit
val add_let_env : Var.t -> ctx -> tm -> unit

val mk_tm : ctx -> tm -> tm * ty
val mk_ty : ctx -> ty -> ty
                           
val checkEqual : ctx -> ty -> ty -> unit



