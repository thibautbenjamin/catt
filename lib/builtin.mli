open Raw_types
open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val ps_comp : int -> ps
val comp_n : int -> Coh.t
val comp : subR -> Coh.t
val arity_comp : subR -> int
val id : Coh.t
val unbiased_unitor : ps -> tm -> Coh.t
