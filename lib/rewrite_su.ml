open Unchecked_types

module M (Coh : sig type t end) =
struct
  open Unchecked_types(Coh)

  let nf _ = assert false
end
