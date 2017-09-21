open ExtSyntax
       
module EVar : sig
  type t =
    |Name of string

  val mk : Var.t -> t
end
			       
type evar = EVar.t

type env
type ctx
type coh

val empty_env : env
val mk_coh : env -> ctx -> expr -> coh
val mk_ctx : env -> (var * expr) list -> ctx
val add_env : env -> evar -> coh -> env
val coh_to_string : coh -> bool -> string

