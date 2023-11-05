open Raw_types
open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val func_codim1_fn : (Coh.t -> Var.t list -> Coh.t) ref
val ps_comp : int -> ps
val comp_n : int -> Coh.t
val comp : subR -> Coh.t
val id : Coh.t
val unbiased_unitor : ps -> tm -> Coh.t
