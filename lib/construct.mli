open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val to_tm : constr -> tm
val to_ty : constr -> ty
val arr : constr -> constr -> ty
val characteristic_sub_ps : constr -> sub_ps
val coh_app : Coh.t -> sub_ps -> constr
val of_coh : Coh.t -> constr
val tm_app : Tm.t -> sub -> constr
val of_tm : Tm.t -> constr
val wcomp : constr -> int -> constr -> constr
val wcomp3 : constr -> int -> constr -> int -> constr -> constr
val intch_comp_nm : constr -> constr -> constr -> constr
val intch_comp_mn : constr -> constr -> constr -> constr
val opposite : constr -> op_data -> constr
val inv : constr -> constr
val functorialise : constr -> Var.t list -> constr
val id : constr -> constr
val id_n : int -> constr -> constr
val dim : constr -> int
val apply_sub : constr -> sub -> constr
val apply_sub_ps : constr -> sub_ps -> constr
val rename : constr -> (Var.t * tm) list -> constr
val bdry : int -> constr -> constr * constr
val src : int -> constr -> constr
val tgt : int -> constr -> constr
val inverse : constr -> constr
val suspend : int -> constr -> constr
val comp_n : constr list -> constr
val comp : constr -> constr -> constr
val comp3 : constr -> constr -> constr -> constr
val op : int list -> constr -> constr
val witness : constr -> constr
val glue_subs_along : int -> 'a list list -> 'a list
val wcomp_n : int -> constr list -> constr
val characteristic_sub_ps_composite : constr list -> sub_ps
