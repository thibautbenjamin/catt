open Common

module type S = sig
  module rec Coh : sig
    type t

    val forget : t -> ps * (t, Tm.t) ty * pp_data
    val check : ps -> (t, Tm.t) ty -> pp_data -> t
    val to_string : ?unroll:bool -> t -> string
    val func_data : t -> (Var.t * int) list list
    val is_equal : t -> t -> bool
  end

  and Tm : sig
    type t

    val develop : t -> (Coh.t, t) tm
    val func_data : t -> (Var.t * int) list list option
    val name : t -> string option
    val full_name : t -> string option
    val ctx : t -> (Coh.t, t) ctx
    val is_equal : t -> t -> bool

    val apply :
      ((Coh.t, Tm.t) ctx -> (Coh.t, t) ctx) ->
      ((Coh.t, t) tm -> (Coh.t, t) tm) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, t) sub
  end
end
