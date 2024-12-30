open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

type op_data = int list

val op_data_to_string : op_data -> string
val equiv_op_ps : ps -> op_data -> sub_ps
val tm : tm -> op_data -> tm
val coh : Coh.t -> op_data -> Coh.t
val sub : sub -> op_data -> sub
val ty : ty -> op_data -> ty
val ctx : ctx -> op_data -> ctx
val checked_tm : Tm.t -> op_data -> Tm.t
