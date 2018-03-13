module Var = struct
  type t =
  |Name of string
  |New of int
	     
  let to_string v =
  match v with
  |Name s -> s
  |New i -> "_" ^ string_of_int i

  let mk s = Name s

  let equal u v = match u,v with
    |Name s, Name s' -> s = s'
    |New a, New b -> a = b
    |_,_ -> false
end
