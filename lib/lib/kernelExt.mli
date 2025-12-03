open Common

module type S = sig
  exception InvalidPS

  val theory : theory

  module rec Coh : sig
    type t
    type innertm = Tm.t

    val ps : t -> PS.t
    val forget : t -> ps * (Coh.t, Tm.t) pty * pp_data
    val suspend : t -> t
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
    val is_inv : t -> bool
    val to_string : ?unroll:bool -> t -> string
    val dim : t -> int
    val src : t -> (Coh.t, Tm.t) ptm
    val tgt : t -> (Coh.t, Tm.t) ptm
    val check : ps -> (Coh.t, Tm.t) pty -> pp_data -> t
    val ty : t -> Ty.t

    val check_noninv :
      ps -> (Coh.t, Tm.t) ptm -> (Coh.t, Tm.t) ptm -> pp_data -> t

    val check_inv : ps -> (Coh.t, Tm.t) ptm -> (Coh.t, Tm.t) ptm -> pp_data -> t

    val noninv_srctgt :
      t -> (Coh.t, Tm.t) ptm * (Coh.t, Tm.t) ptm * (Coh.t, Tm.t) pty

    val func_data : t -> (Var.t * int) list list

    val apply_ps :
      (ps -> ps) ->
      ((Coh.t, Tm.t) pty -> (Coh.t, Tm.t) pty) ->
      (pp_data -> pp_data) ->
      t ->
      t

    val apply :
      ((Coh.t, Tm.t) pctx -> (Coh.t, Tm.t) pctx) ->
      ((Coh.t, Tm.t) pty -> (Coh.t, Tm.t) pty) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, Tm.t) psub
  end

  and Ty : sig
    type t
    and expr = Obj | Arr of t * Tm.t * Tm.t

    val expr : t -> expr
  end

  and Tm : sig
    type t

    val typ : t -> Ty.t
    val ty : t -> (Coh.t, Tm.t) pty
    val forget : t -> (Coh.t, Tm.t) ptm
    val constr : t -> (Coh.t, Tm.t) pconstr
    val ctx : t -> (Coh.t, Tm.t) pctx
    val name : t -> string option
    val full_name : t -> string option
    val func_data : t -> (Var.t * int) list list option
    val of_coh : Coh.t -> t
    val develop : t -> (Coh.t, Tm.t) ptm
    val pp_data : t -> pp_data option
    val to_string : t -> string
    val is_equal : t -> t -> bool

    val check :
      (Coh.t, Tm.t) pctx ->
      ?ty:(Coh.t, Tm.t) pty ->
      ?name:pp_data ->
      (Coh.t, Tm.t) ptm ->
      t

    val apply :
      ((Coh.t, Tm.t) pctx -> (Coh.t, Tm.t) pctx) ->
      ((Coh.t, Tm.t) ptm -> (Coh.t, Tm.t) ptm) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, Tm.t) psub
  end

  and PS : sig
    type t = ps
    type inner_ctx = Ctx.t

    val mk : inner_ctx -> t
  end

  and Ctx : sig
    type t

    val check : (Coh.t, Tm.t) pctx -> t
    val to_string : t -> string
    val forget : t -> (Coh.t, Tm.t) pctx
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
  end

  module Sub : sig
    type t
  end

  type ty = (Coh.t, Tm.t) pty
  type tm = (Coh.t, Tm.t) ptm
  type sub = (Coh.t, Tm.t) psub
  type sub_ps = (Coh.t, Tm.t) psub_ps
  type ctx = (Coh.t, Tm.t) pctx
  type constr = (Coh.t, Tm.t) pconstr
  type meta_ctx = (int * ty) list
  type value = (Coh.t, Tm.t) pvalue
  type decls = (value * string) list

  module Core :
    Core.S
      with type PS.t = PS.t
       and type Coh.t = Coh.t
       and type Tm.t = Tm.t
       and type Ty.t = Ty.t

  include module type of Syntax.Make (Core)

  val check_term : Ctx.t -> ?ty:ty -> ?name:pp_data -> tm -> Tm.t
  val check_constr : ?name:pp_data -> ctx -> constr -> Tm.t
  val check_coh : ps -> ty -> pp_data -> Coh.t
  val check_sub : ctx -> sub -> ctx -> unit
end
