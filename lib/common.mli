type ps = Br of ps list

(* Internal representation of a functorialisation: each position in
   the list is a locally maximal variable and each integer indicates
   how many time the corresponding position is functorialised *)
type functorialisation_data = int list
type coh_pp_data = string * int * functorialisation_data option

type strictness_lv =
  | Wk

module type StrictnessLv =
sig
  val
    lv : strictness_lv
end
module Wk : StrictnessLv

exception NotEqual of string * string
exception DoubledVar of string
exception WrongNumberOfArguments
