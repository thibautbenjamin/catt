open Common
open Raw_types

module Make (Environment : Environments.S) : sig
  open Environment.K

  val ctx : (Var.t * tyR) list -> ctx
  val ty : (Var.t * tyR) list -> tyR -> ctx * ty
  val tm : (Var.t * tyR) list -> tmR -> ctx * tm
  val ty_in_ps : (Var.t * tyR) list -> tyR -> ps * ty
end
