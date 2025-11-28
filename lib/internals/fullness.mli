module Make : functor (K : KernelSignature.S) -> sig
  open K

  type res = Inv | NonInv of Tm.t * Tm.t | No

  val check : PS.t -> Ty.t -> res
end
