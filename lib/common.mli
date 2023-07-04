module Var : sig
  type t =
    | Name of string
    | New of int
    | Db of int

  val to_string : t -> string
  val make_var : string -> t
  val check_equal : t -> t -> unit
  val increase_lv : t -> int -> int -> t
  val suspend : t -> t
end

type ps = Br of ps list

type ty =
  | Meta_ty of int
  | Obj
  | Arr of ty * tm * tm
and tm =
  | Var of Var.t
  | Meta_tm of int
  | Coh of ps * ty * sub_ps
and sub_ps = tm list

type ctx = (Var.t * (ty * bool)) list

type sub = (Var.t * tm) list

type meta_ctx = ((int * ty) list)
