exception UnknownId of string
module Var : sig
  type t =
    |Name of string
    |New of string * int
end
type var = Var.t
type env
type sub
type ctx
type ps
      
module Expr : sig
  type t =
    |Var of var
    |Obj
    |Arr of t * t * t
    |PArr of t * t
    |Coh of ps * t
    |Sub of t * sub
end

type expr = Expr.t

val empty_ctx : ctx
val empty_env : env
val mk_ps : ctx -> ps
val mk_sub : env -> expr list -> ctx -> ctx -> sub
val add_env : env -> var -> expr -> env
val add_ctx : (env * ctx) -> var -> expr -> (env * ctx)
val to_string : expr -> bool -> bool -> string
					  
(** To be removed : For debugging purposes*)
val string_of_ctx : ctx -> string                                             
