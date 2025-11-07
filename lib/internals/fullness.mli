open Common

module type FArgs = sig
  module Theory : Theory.S

  module Coh : sig
    type t
  end

  module Ctx : sig
    type t

    val domain : t -> Var.t list
  end

  module rec Sub : sig
    type t = private {
      list : Tm.t list;
      src : Ctx.t;
      tgt : Ctx.t;
      unchecked : (Coh.t, Tm.t) sub;
    }
  end

  and Ty : sig
    type t = private { c : Ctx.t; e : expr; unchecked : (Coh.t, Tm.t) ty }
    and expr = Obj | Arr of t * Tm.t * Tm.t

    val dim : t -> int
  end

  and Tm : sig
    type expr = Var of Var.t | Coh of Coh.t * Sub.t | App of Tm.t * Sub.t

    and t = private {
      ty : Ty.t;
      e : expr;
      unchecked : (Coh.t, t) tm;
      mutable developped : (Coh.t, t) tm option;
      name : pp_data option;
    }

    val preimage : t -> Sub.t -> t
  end

  module PS : sig
    type t

    val source : t -> Sub.t
    val target : t -> Sub.t
  end
end

module Make : functor (A : FArgs) -> sig
  open A

  type res = Inv | NonInv of Tm.t * Tm.t | No

  val check : PS.t -> Ty.t -> res
end
