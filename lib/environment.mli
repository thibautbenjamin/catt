type value =
  | Coh of Unchecked.ps * Unchecked.ty
  | Tm of Unchecked.ctx * Unchecked.tm

type t

val add_let : Variables.var -> Unchecked.ctx -> Unchecked.tm -> unit
val add_coh : Variables.var -> Unchecked.ps -> Unchecked.ty -> unit
val val_var : Variables.var -> value
