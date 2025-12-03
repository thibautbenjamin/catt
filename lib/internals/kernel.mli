open Common

(* Like a functor but returns a first class module, as it enforces the invariant
that there is at most one kernel for a given theory. *)
val make : theory -> (module KernelExt.S)
