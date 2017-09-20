module Var : sig
  type t =
    |Name of string

  val to_string : t -> string
  end
type var = Var.t
	       
type expr =
  |Var of var
  |Obj
  |Arr of expr * expr
  |Coh of ((var * expr) list) * expr
  |Sub of expr * (expr list)
val string_of_expr : expr -> string
	       
module EVar : sig
  type t =
    |Name of string

  val mk : var -> t
end
			       
type evar = EVar.t

type env
type sub
type ctx
type ps
type coh
type cut
type nexpr


	      
val empty_ctx : ctx
val empty_env : env
val mk_ps : ctx -> ps
val mk_sub : env -> expr list -> ctx -> ctx -> sub
val mk_coh : env -> ctx -> expr -> coh
val mk_ctx : env -> (var * expr) list -> ctx
val mk_nexpr : env -> ctx -> expr -> nexpr
val add_env : env -> evar -> coh -> env
val add_ctx : env -> ctx -> var -> expr -> ctx
val in_ctx : ctx -> var -> bool 
val nexpr_to_string : nexpr -> bool -> string
val coh_to_string : coh -> bool -> string


				     
(** To be removed : For debugging purposes*)
val string_of_ctx : ctx -> string                                             
