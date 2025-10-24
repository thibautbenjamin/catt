exception NotEqual of string * string
exception DoubledVar of string
exception WrongNumberOfArguments
exception NotInImage

type ps = Br of ps list

module Var : sig
  type t =
    | Name of string
    | New of int
    | Db of int (* storing de Bruijn levels for coherences *)
    | Plus of t (* x+ funct. copy of var x *)
    | Bridge of t (* x~ funct. var of x *)

  val to_string : t -> string
  val make_var : string -> t
  val is_equal : t -> t -> bool
  val suspend : t -> t
  val suspend_n : t -> int -> t
  val fresh : unit -> t
end

type ('a, 'b) ty =
  | Meta_ty of int
  | Obj
  | Arr of ('a, 'b) ty * ('a, 'b) tm * ('a, 'b) tm

and ('a, 'b) tm =
  | Var of Var.t
  | Meta_tm of int
  | Coh of 'a * ('a, 'b) sub_ps
  | App of 'b * ('a, 'b) sub

and ('a, 'b) sub_ps = (('a, 'b) tm * bool) list
and ('a, 'b) sub = (Var.t * (('a, 'b) tm * bool)) list

type ('a, 'b) ctx = (Var.t * (('a, 'b) ty * bool)) list
type ('a, 'b) meta_ctx = (int * ('a, 'b) ty) list
type ('a, 'b) constr = ('a, 'b) tm * ('a, 'b) ty
type pp_data = string * int * (Var.t * int) list list

val take : int -> 'a list -> 'a list

type op_data = int list

(* For managing theories *)
type strictness = Weak | Idempotent | Units | UAssociators
type invertibility = int option
type postulates = TerminalObject

type theory = {
  strictness : strictness;
  invertibility : invertibility;
  postulates : postulates list;
}

val vanilla_theory : theory
