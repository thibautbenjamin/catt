open Common
module M (S : StrictnessLv)
= struct
  module Kernel = Kernel.M(S)
  module Unchecked = Kernel.Unchecked

  let ctx c _  = c
  let ty c _ t = c,t
  let tm c _ t =  c,t
end
