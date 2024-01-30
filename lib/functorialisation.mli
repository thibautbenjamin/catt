open Common
open Kernel
open Kernel.Unchecked_types

val coh : Coh.t -> functorialisation_data -> Coh.t
val tm : ctx -> tm -> functorialisation_data -> ctx * tm
