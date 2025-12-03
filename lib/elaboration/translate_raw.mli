open Common
open Raw_types

module Make (Environment : Environments.S) : sig
  open Environment.K

  val tm : tmR -> tm * meta_ctx
  val ty : tyR -> ty * meta_ctx
  val ctx : (Var.t * tyR) list -> ctx * meta_ctx
  val sub_to_suspended : sub_ps -> sub_ps * meta_ctx
end
