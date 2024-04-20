open Raw_types
open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

val ps_comp : int -> ps
val comp_n : int -> Coh.t
val comp : subR -> Coh.t
val whisk : int -> int -> int -> Coh.t
val whisk_sub_ps : int -> tm -> ty -> tm -> ty -> sub_ps
val comp_kn_tm : int -> int -> tm
val comp_n_tm : int -> tm
val ccomp : subR -> tm
val id : Coh.t
val unbiased_unitor : ps -> tm -> Coh.t

(* returns the associator pairing up the middle two cells of a composite of
    (2*k) 1-cells. The argument is the integer k *)
val middle_associator : int -> Coh.t

(* returns the unitor cancelling the identity in the middle of a composite of
(2*k+1) 1-cells. The argument is the integer k *)
val middle_unitor : int -> Coh.t

(* returns the whiskering rewriting the middle term of a composite of (2*k+1)
    1-cells. The argument is the integer k *)
val middle_rewrite : int -> Coh.t
