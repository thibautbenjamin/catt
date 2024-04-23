open Common
module M(S : StrictnessLv)
  : sig
    open Kernel.M(S)
    open Unchecked_types

    val new_ty : unit -> ty
    val new_tm : unit -> tm * (int * ty)
  end
