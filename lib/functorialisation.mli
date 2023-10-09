open Kernel
open Kernel.Unchecked_types

val coh : coh -> functorialisation_data -> coh
val tm : ctx -> tm -> functorialisation_data -> ctx * tm
