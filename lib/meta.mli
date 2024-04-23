open Common
module Meta (Strictness : StrictnessLv)
  : sig
    open Kernel.Kernel(Strictness)
    open Unchecked_types

    val new_ty : unit -> ty
    val new_tm : unit -> tm * (int * ty)
  end
