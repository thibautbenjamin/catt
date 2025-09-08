open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

type constr = tm * ty

val wcomp : constr -> int -> constr -> constr
val wcomp3 : constr -> int -> constr -> int -> constr -> constr
val intch_comp_nm : constr -> constr -> constr -> constr
val intch_comp_mn : constr -> constr -> constr -> constr
val opposite : constr -> op_data -> constr
val inv : constr -> constr
