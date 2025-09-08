open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

type op_data = int list

val op_data_to_string : op_data -> string
val equiv_op_ps : ps -> op_data -> sub_ps
val tm : tm -> op_data -> tm
val coh : Coh.t -> op_data -> Coh.t
