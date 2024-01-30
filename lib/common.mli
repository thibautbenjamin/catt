(* Internal representation of a functorialisation: each position in
   the list is a locally maximal variable and each integer indicates
   how many time the corresponding position is functorialised *)
type functorialisation_data = int list

exception NotEqual of string * string
