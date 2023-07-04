open Common

val tm : Kernel.Ctx.t -> Syntax.tm -> tm
val sub : Kernel.Ctx.t -> Syntax.tm list -> ctx -> sub
val ty : Kernel.Ctx.t -> Syntax.ty -> ty
val ctx : (Var.t * Syntax.ty) list -> ctx
