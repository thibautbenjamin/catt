open Common

val ctx : (Var.t * Syntax.ty) list -> ctx
val ty : Syntax.ty -> ty
val tm : Syntax.tm -> tm
val ty_in_ps : (Var.t * Syntax.ty) list -> Syntax.ty -> ty
val ps : (Var.t * Syntax.ty) list -> ps
