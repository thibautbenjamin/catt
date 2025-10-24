open Common

module type S = sig
  val theory : theory
  val environment_created : bool ref
end

val make : theory -> (module S)
