open Common
module M (S : StrictnessLv)
  : sig
    open Kernel.M(S)
    open Unchecked_types
    open Raw_types

    val ctx : (Var.t * tyR) list -> ctx
    val ty : (Var.t * tyR) list -> tyR -> ctx * ty
    val tm : (Var.t * tyR) list -> tmR -> ctx * tm
    val ty_in_ps : (Var.t * tyR) list -> tyR -> ps * ty
end
