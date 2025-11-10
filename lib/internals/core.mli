open Common

module type S = sig
  module PS : sig
    type t = ps
  end

  module Coh : sig
    type t
    type innertm

    val suspend : t -> t
    val forget : t -> ps * (t, innertm) ty * pp_data
    val to_string : ?unroll:bool -> t -> string
    val func_data : t -> (Var.t * int) list list
    val is_equal : t -> t -> bool
  end

  module Tm : sig
    type t

    val develop : t -> (Coh.t, t) tm
    val func_data : t -> (Var.t * int) list list option
    val name : t -> string option
    val full_name : t -> string option
    val ctx : t -> (Coh.t, t) ctx
    val is_equal : t -> t -> bool
    val to_var : t -> Var.t

    val check :
      (Coh.t, t) ctx -> ?ty:(Coh.t, t) ty -> ?name:pp_data -> (Coh.t, t) tm -> t

    val ty : t -> (Coh.t, t) ty
    val forget : t -> (Coh.t, t) tm

    val apply :
      ((Coh.t, t) ctx -> (Coh.t, t) ctx) ->
      ((Coh.t, t) tm -> (Coh.t, t) tm) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, t) sub
  end

  module Ty : sig
    type t

    val to_string : t -> string
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
    val forget : t -> (Coh.t, Tm.t) ty
    val check_with_ctx : (Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ty -> t
  end
end
