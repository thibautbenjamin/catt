open Common

module Make (C : Core.S) : sig
  open C

  val ps_to_string : ps -> string
  val ty_to_string : ty -> string
  val tm_to_string : tm -> string
  val sub_ps_to_string : ?func:(Var.t * int) list list -> sub_ps -> string
  val ctx_to_string : ctx -> string
  val sub_to_string : ?func:(Var.t * int) list list -> sub -> string
  val sub_to_string_debug : sub -> string
  val meta_ctx_to_string : meta_ctx -> string
  val full_name : pp_data -> string
  val pp_data_to_string : ?print_func:bool -> pp_data -> string
  val print_kolmogorov : tm -> string
end
