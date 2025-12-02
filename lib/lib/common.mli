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

type pp_data = string * int * (Var.t * int) list list

type ('a, 'b) pty =
  | Meta_ty of int
  | Obj
  | Arr of ('a, 'b) pty * ('a, 'b) ptm * ('a, 'b) ptm

and ('a, 'b) ptm =
  | Var of Var.t
  | Meta_tm of int
  | Coh of 'a * ('a, 'b) psub_ps
  | App of 'b * ('a, 'b) psub

and ('a, 'b) psub_ps = (('a, 'b) ptm * bool) list
and ('a, 'b) psub = (Var.t * (('a, 'b) ptm * bool)) list

type ('a, 'b) pctx = (Var.t * (('a, 'b) pty * bool)) list
type ('a, 'b) pconstr = ('a, 'b) ptm * ('a, 'b) pty
type ('a, 'b) pvalue = VCoh of 'a | VTm of 'b

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
