exception UnknownId of string
exception UnknownCoh of string
exception IsNotType of string	      
exception HasNoType of string	      
exception NotEqual of string * string
			 
module Var : sig
  type t =
    |Name of string
    |New of string * int
  end

module EVar : sig
  type t =
    |Name of string
    |New of string * int
  end
			       
type var = Var.t
type evar = EVar.t

type env
type sub
type ctx
type ps
type coh
      
module Expr : sig
  type t =
    |CVar of var
    |Obj
    |Arr of t * t * t
    |PArr of t * t
    |Sub of ecoh * sub
   and ecoh =
    |Fold of evar
    |Unfold of coh
end

type expr = Expr.t

	      
val empty_ctx : ctx
val empty_env : env
val mk_ps : ctx -> ps
val mk_sub : env -> expr list -> ctx -> ctx -> sub
val mk_coh : env -> ps -> expr -> coh
val add_env : env -> evar -> coh -> env
val add_ctx : env -> ctx -> var -> expr -> ctx
val in_ctx : ctx -> var -> bool 
val expr_to_string : expr -> bool -> bool -> string
val coh_to_string : coh -> bool -> bool -> string
					  
(** To be removed : For debugging purposes*)
val string_of_ctx : ctx -> string                                             
