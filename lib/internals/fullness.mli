module Make : functor
  (_ : Theory.S)
  (Sub : sig
     type t
   end)
  (PS : sig
     type t

     val source : t -> Sub.t
     val target : t -> Sub.t
   end)
  (Tm : sig
     type t

     val preimage : t -> Sub.t -> t
     val contains_all_vars : t -> bool
   end)
  (Ty : sig
     type t

     val dim : t -> int
     val retrieve_arrow : t -> Tm.t * Tm.t
     val contains_all_vars : t -> bool
   end)
  -> sig
  type res = Inv | NonInv of Tm.t * Tm.t | No

  val check : PS.t -> Ty.t -> res
end
