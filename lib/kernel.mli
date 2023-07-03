module Ctx : sig
  type t

  val _check : Unchecked.ctx -> t
  val _forget : t -> Unchecked.ctx
end

module Ty : sig
  type t

  val _from_unchecked : Ctx.t -> Unchecked.ty -> t
  val _forget : t -> Unchecked.ty
end

module Tm : sig
  type t

  val check : Ctx.t -> ?ty : Unchecked.ty -> Unchecked.tm -> t
  val _forget : t -> Unchecked.tm

  val typ : t -> Ty.t
end

module PS : sig
  type t

  val mk : Ctx.t -> t
  val check : Unchecked.ps -> t
  val _forget : t -> Unchecked.ps
end

module Coh : sig
  type t

  val check : Unchecked.ps -> Unchecked.ty -> (Variables.t * int) list -> t
end
