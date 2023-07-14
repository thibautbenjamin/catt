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
