open Common
module M (S : StrictnessLv)
= struct
  module type ElabSig =
  sig
    open Kernel.M(S)
    open Unchecked_types
    open Raw_types

    val ctx : (Var.t * tyR) list -> ctx
    val ty : (Var.t * tyR) list -> tyR -> ctx * ty
    val tm : (Var.t * tyR) list -> tmR -> ctx * tm
    val ty_in_ps : (Var.t * tyR) list -> tyR -> ps * ty
  end

  let elab_module =
    match S.lv with
    | Wk -> (module Elaborate_wk.M(S) : ElabSig)

  let ctx =
    let module Elab = (val elab_module) in
    Elab.ctx

  let ty =
    let module Elab = (val elab_module) in
    Elab.ty

  let tm =
    let module Elab = (val elab_module) in
    Elab.tm

  let ty_in_ps =
    let module Elab = (val elab_module) in
    Elab.ty_in_ps

end
