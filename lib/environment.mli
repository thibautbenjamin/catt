type value =
  | Coh of Unchecked.ps * Unchecked.ty
  | Tm of Unchecked.ctx * Unchecked.tm

type t

val add_let : Variables.t -> Unchecked.ctx -> Unchecked.tm -> unit
val add_let_check : Variables.t -> Unchecked.ctx -> Unchecked.tm -> Unchecked.ty -> unit
val add_coh : Variables.t -> Unchecked.ps -> Unchecked.ty -> unit
val val_var : Variables.t -> value
