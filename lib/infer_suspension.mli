open Common
open Raw_types
module M (_ : StrictnessLv)
  :sig
    val tm : (Var.t * tyR) list ->  tmR -> tmR
    val ty : (Var.t * tyR) list -> tyR -> tyR
    val dim_tm : (Var.t * tyR) list ->  tmR -> int
  end
