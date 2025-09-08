open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

type constr = tm * ty

val wcomp : constr -> int -> constr -> constr
val intch_comp_nm : constr -> constr -> constr -> constr
val inv : constr -> constr
