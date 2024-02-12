open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val coh : Coh.t -> functorialisation_data -> Coh.t
val coh_all : Coh.t -> Coh.t
val tm : ctx -> tm -> functorialisation_data -> ctx * tm
