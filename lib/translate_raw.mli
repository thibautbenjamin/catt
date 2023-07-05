open Common

val tm : Syntax.tm -> tm * meta_ctx
val sub : Syntax.tm list -> ctx -> sub * meta_ctx
val ty : Syntax.ty -> ty * meta_ctx
val ctx : (Var.t * Syntax.ty) list -> ctx * meta_ctx
val sub_to_suspended : sub_ps -> sub_ps * meta_ctx
