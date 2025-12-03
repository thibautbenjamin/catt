module Make : functor (C : Core.S) -> sig
  module Unchecked : module type of Unchecked.Make (C)
  module Display_maps : module type of Display_maps.Make (C)
  module Printing : module type of Printing.Make (C)
  module Equality : module type of Equality.Make (C)
end
