open ExtSyntax
       
type env
type kexpr
type ctx
       
val empty_env : env
val add_env : env -> var -> expr -> env

val checkType : env -> ctx -> kexpr -> kexpr -> unit
val mk_expr : env -> ctx -> expr -> kexpr
val mk_ctx : env -> (var * expr) list -> ctx
 
