module Make (Core : Core.S) : sig
  open Core
  open Common

  val ps_to_string : ps -> string
  val ty_to_string : (Coh.t, Tm.t) ty -> string
  val tm_to_string : (Coh.t, Tm.t) tm -> string

  val sub_ps_to_string :
    ?func:(Var.t * int) list list -> (Coh.t, Tm.t) sub_ps -> string

  val ctx_to_string : (Coh.t, Tm.t) ctx -> string

  val sub_to_string :
    ?func:(Var.t * int) list list -> (Coh.t, Tm.t) sub -> string

  val sub_to_string_debug : (Coh.t, Tm.t) sub -> string
  val meta_ctx_to_string : (Coh.t, Tm.t) meta_ctx -> string
  val full_name : pp_data -> string
  val pp_data_to_string : ?print_func:bool -> pp_data -> string
  val print_kolmogorov : (Coh.t, Tm.t) tm -> string
end
