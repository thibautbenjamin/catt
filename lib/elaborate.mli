open Common

val ctx : (Var.t * Syntax.ty) list -> ctx
val ty : (Var.t * Syntax.ty) list -> Syntax.ty -> ctx * ty
val tm : (Var.t * Syntax.ty) list -> Syntax.tm -> ctx * tm
val ty_in_ps : (Var.t * Syntax.ty) list -> Syntax.ty -> ps * ty
