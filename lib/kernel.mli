module Ctx : sig
  type t

  val check : Unchecked.ctx -> t
end

module Ty : sig
  type t

  val forget : t -> Unchecked.ty
end

module Tm : sig
  type t

  val check : Ctx.t -> ?ty : Unchecked.ty -> Unchecked.tm -> t
  val typ : t -> Ty.t
end

module PS : sig
  type t

  val mk : Ctx.t -> t
  val forget : t -> Unchecked.ps
end

module Coh : sig
  type t

  val check : Unchecked.ps -> Unchecked.ty -> (Variables.t * int) list -> t
end
