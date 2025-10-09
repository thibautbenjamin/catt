module Make (Core : Core.S) = struct
  open Core

  type ty = (Coh.t, Tm.t) Common.ty
  type tm = (Coh.t, Tm.t) Common.tm
  type sub_ps = (Coh.t, Tm.t) Common.sub_ps
  type sub = (Coh.t, Tm.t) Common.sub
  type ctx = (Coh.t, Tm.t) Common.ctx
  type meta_ctx = (Coh.t, Tm.t) Common.meta_ctx
  type constr = (Coh.t, Tm.t) Common.constr

  module Unchecked = Unchecked.Make (Core)
  module Display_maps = Display_maps.Make (Core)
  module Printing = Printing.Make (Core)
  module Equality = Equality.Make (Core)
end
