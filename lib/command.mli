open Kernel
open Raw_types

type cmd =
  | Coh of Var.t * (Var.t * tyR) list * tyR
  | Check of ((Var.t * tyR) list) * tmR * tyR option
  | Decl of Var.t * (Var.t * tyR) list * tmR * tyR option
  | Set of string * string

type prog = cmd list

val exec : loop_fn:(unit -> unit) -> prog -> unit
