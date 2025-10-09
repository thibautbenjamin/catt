module Make : functor (Core : Core.S) -> sig
  open Core

  type ty = (Coh.t, Tm.t) Common.ty
  type tm = (Coh.t, Tm.t) Common.tm
  type sub_ps = (Coh.t, Tm.t) Common.sub_ps
  type sub = (Coh.t, Tm.t) Common.sub
  type ctx = (Coh.t, Tm.t) Common.ctx
  type meta_ctx = (Coh.t, Tm.t) Common.meta_ctx
  type constr = (Coh.t, Tm.t) Common.constr

  module Unchecked : module type of Unchecked.Make (Core)
  module Display_maps : module type of Display_maps.Make (Core)
  module Printing : module type of Printing.Make (Core)
  module Equality : module type of Equality.Make (Core)
end
