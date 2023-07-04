open Common

val ps_to_string : ps -> string
val ty_to_string : ty -> string
val tm_to_string : tm -> string
val sub_ps_to_string : sub_ps -> string
val ctx_to_string : ctx -> string
val sub_to_string : sub -> string
val check_equal_ps : ps -> ps -> unit
val check_equal_ty : ty -> ty -> unit
val check_equal_tm : tm -> tm -> unit
val check_equal_sub_ps : sub_ps -> sub_ps -> unit
val check_equal_ctx : ctx -> ctx -> unit
val var_apply_sub : Var.t -> sub -> tm
val tm_apply_sub : tm -> sub -> tm
val ty_apply_sub : ty -> sub -> ty
val sub_apply_sub : sub -> sub -> sub
val rename_ty : ty -> (Var.t * int) list -> ty
val db_levels : ctx -> ctx * (Var.t * int) list * int
val ps_to_ctx : ps -> ctx
