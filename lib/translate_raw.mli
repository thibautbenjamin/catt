open Common

val tm : Syntax.tm -> tm
val sub : Syntax.tm list -> ctx -> sub
val ty : Syntax.ty -> ty
val ctx : (Var.t * Syntax.ty) list -> ctx
