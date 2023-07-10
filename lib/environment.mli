open Common

type value =
  | Coh of ps * ty
  | Tm of ctx * tm

type t

val add_let : Var.t -> ctx -> ?ty:ty -> tm -> unit
val add_coh : Var.t -> ps -> ty -> unit
val val_var : Var.t -> value
