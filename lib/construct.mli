open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

type constr = tm * ty
val to_tm : constr -> tm
val to_ty : constr -> ty
val arr : constr -> constr -> ty
val characteristic_sub_ps : constr -> sub_ps
val wcomp : constr -> int -> constr -> constr
val wcomp3 : constr -> int -> constr -> int -> constr -> constr
val intch_comp_nm : constr -> constr -> constr -> constr
val intch_comp_mn : constr -> constr -> constr -> constr
val opposite : constr -> op_data -> constr
val inv : constr -> constr
val id : constr -> constr
val id_n : int -> constr -> constr
val dim : constr -> int
val apply_sub : constr -> sub -> constr
val apply_sub_ps : constr -> sub_ps -> constr
val bdry : int -> constr -> constr*constr
val _src : int -> constr -> constr
val tgt : int -> constr -> constr
val inverse : constr -> constr
val suspend : int -> constr -> constr
val comp_n : constr list -> constr
val op : int list -> constr -> constr
val witness : constr -> constr
val glue_subs_along : int -> 'a list list -> 'a list
val wcomp_n : int -> constr list -> constr
val characteristic_sub_ps_composite : constr list -> sub_ps
