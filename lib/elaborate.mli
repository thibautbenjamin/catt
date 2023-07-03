val ctx : (Var.t * Syntax.ty) list -> Unchecked.ctx
val ty : Unchecked.ctx -> Syntax.ty -> Unchecked.ty
val tm : Unchecked.ctx -> Syntax.tm -> Unchecked.tm
val ty_in_ps : (Var.t * Syntax.ty) list -> Syntax.ty -> Unchecked.ty
val ps : (Var.t * Syntax.ty) list -> Unchecked.ps
