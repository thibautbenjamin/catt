type pshape =
  |PNil
  |PCons of pshape
  |PDrop of pshape

let rec string_of_pshape p =
  match p with
  |PNil -> "o"
  |PCons p -> Printf.sprintf "%s []" (string_of_pshape p)
  |PDrop p -> Printf.sprintf "%s !" (string_of_pshape p)
