open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val pad : constr -> constr -> Tm.t -> Var.t -> sub -> constr

val repad :
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  constr ->
  Tm.t ->
  sub ->
  sub ->
  Var.t ->
  sub ->
  constr

val repad_old :
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
