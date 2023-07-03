type value =
  | Coh of Unchecked.ps * Unchecked.ty
  | Tm of Unchecked.ctx * Unchecked.tm

type t

val add_let : Var.t -> Unchecked.ctx -> Unchecked.tm -> unit
val add_let_check : Var.t -> Unchecked.ctx -> Unchecked.tm -> Unchecked.ty -> unit
val add_coh : Var.t -> Unchecked.ps -> Unchecked.ty -> unit
val val_var : Var.t -> value
