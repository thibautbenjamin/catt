open ExtSyntax
       
type env
type kexpr
type ctx
       
val init_env : unit
val add_env : var -> expr -> unit

val checkType : ctx -> kexpr -> kexpr -> unit
val infer : ctx -> kexpr -> kexpr
val string_of_kexpr : kexpr -> string
val mk_expr : ctx -> expr -> kexpr
val mk_ctx : (var * expr) list -> ctx
 
