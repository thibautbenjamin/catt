open Common

val ps_to_string : ps -> string
val ty_to_string : ty -> string
val tm_to_string : tm -> string
val sub_ps_to_string : sub_ps -> string
val ctx_to_string : ctx -> string
val sub_to_string : sub -> string
val meta_ctx_to_string : meta_ctx -> string
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
val rename_tm : tm -> (Var.t * int) list -> tm
val db_levels : ctx -> ctx * (Var.t * int) list * int
val ps_to_ctx : ps -> ctx
val sub_ps_to_sub : sub_ps -> ps -> sub * ctx
val two_fresh_vars : ctx -> Var.t * Var.t
val identity : ctx -> sub
val identity_ps : ctx -> sub_ps
val tm_contains_vars : tm -> Var.t list -> bool
val dim_ty : ty -> int
val dim_ctx : ctx -> int
val dim_ps : ps -> int
