module Make (C : Core.S) = struct
  module Unchecked = Unchecked.Make (C)
  module Display_maps = Display_maps.Make (C)
  module Printing = Printing.Make (C)
  module Equality = Equality.Make (C)
end
