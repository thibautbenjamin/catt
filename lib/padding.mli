open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val pad : constr -> constr -> constr -> Var.t -> sub -> constr

val repad :
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  sub ->
  sub ->
  Var.t ->
  sub ->
  constr
