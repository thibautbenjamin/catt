open Common
module M (S : StrictnessLv)
  : sig
    open Kernel.M(S)
    open Unchecked_types

    val ctx : int -> ctx
    val telescope : int -> tm
  end
