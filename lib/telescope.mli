open Common
module Telescope (Strictness : StrictnessLv)
  : sig
    open Kernel.Kernel(Strictness)
    open Unchecked_types

    val ctx : int -> ctx
    val telescope : int -> tm
    val checked : int -> Tm.t
  end
