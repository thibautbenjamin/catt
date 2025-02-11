open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val var_apply_sub : Var.t -> sub -> Var.t
val pullback : ctx -> sub -> ctx -> sub -> ctx * sub
val glue : sub -> sub -> sub -> ctx -> sub -> sub
