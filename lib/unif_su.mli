open Common
module M (S : StrictnessLv)
  : sig
    open Kernel.M(S)
    open Unchecked_types

    val ctx : ctx -> meta_ctx -> ctx
    val ty : ctx -> meta_ctx -> ty -> ctx * ty
    val tm : ctx -> meta_ctx -> tm -> ctx * tm
end
