open Common

module Make (C : Core.S) : sig
  open C

  val var_apply_sub : Var.t -> sub -> Var.t
  val pullback : ctx -> sub -> ctx -> sub -> ctx * sub
  val glue : sub -> sub -> sub -> ctx -> sub -> sub
  val pp_data_rename : pp_data -> sub -> pp_data
end
