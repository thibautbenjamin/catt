open Common

module Ctx : sig
  type t

  val check : ctx -> t
end

module Ty : sig
  type t

  val forget : t -> ty
end

module Tm : sig
  type t

  val check : Ctx.t -> ?ty : ty -> tm -> t
  val typ : t -> Ty.t
end

module PS : sig
  type t

  val mk : Ctx.t -> t
  val forget : t -> ps
end

module Coh : sig
  type t

  val check : ps -> ty -> (Var.t * int) list -> t
end
