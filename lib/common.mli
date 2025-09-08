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
  val check_equal : t -> t -> unit
  val suspend : t -> t
  val suspend_n : t -> int -> t
  val fresh : unit -> t
end

type pp_data = string * int * (Var.t * int) list list
