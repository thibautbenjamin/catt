open Common

val tm : (Var.t * Syntax.ty) list -> Syntax.tm -> tm * meta_ctx
val sub : (Var.t * Syntax.ty) list -> Syntax.tm list -> ctx -> sub * meta_ctx
val ty : (Var.t * Syntax.ty) list -> Syntax.ty -> ty * meta_ctx
val ctx : (Var.t * Syntax.ty) list -> ctx * meta_ctx
val sub_to_suspended : sub_ps -> sub_ps * meta_ctx
