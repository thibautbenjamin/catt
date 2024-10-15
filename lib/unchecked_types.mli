open Common

module type Unchecked_types_sig = functor
  (Coh : sig type t end)
  (Tm : sig type t end)
  -> sig
    type ty = Meta_ty of int | Obj | Arr of ty * tm * tm
    and tm = Var of Var.t | Meta_tm of int | Coh of Coh.t * sub_ps | App of Tm.t * sub
    and sub_ps = (tm * bool) list
    and sub = (Var.t * tm) list

    type ctx = (Var.t * (ty * bool)) list
    type meta_ctx = (int * ty) list
  end

module Unchecked_types : Unchecked_types_sig
