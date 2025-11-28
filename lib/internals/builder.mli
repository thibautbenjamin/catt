module CoreSignature = Core

exception IsObj
exception IsCoh
exception InvalidSubTarget of string * string
exception MetaVariable

module Make : functor (Core : Core.S) -> sig
  open Core

  module Ctx :
    KernelSignature.CtxS
      with type checked_ty = Ty.t
       and type checked_tm = Tm.t
       and type checked_coh = Coh.t
       and type checked_ps = PS.t

  module Sub :
    KernelSignature.SubS
      with type checked_tm = Tm.t
       and type checked_coh = Coh.t
       and type checked_ctx = Ctx.t
end
