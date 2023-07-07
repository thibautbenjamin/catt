module List : sig
  include module type of List

  val remove : 'a -> ('a list) -> 'a list
  val union : ('a list) -> ('a list) -> 'a list
  val unions : ('a list) list -> 'a list
  val included : ('a list) -> ('a list) -> bool
  val set_equal : ('a list) -> ('a list) -> bool
  val diff : ('a list) -> ('a list) -> 'a list
  val get : int -> ('a list) -> 'a
  val map_both : ('a -> 'b) -> ('a * 'a) list -> ('b * 'b) list
  val map_right : ('b -> 'c) -> ('a * 'b) list -> ('a * 'c) list
end
