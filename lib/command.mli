open Kernel
open Syntax

type cmd =
  | Coh of Var.t * (Var.t * tyR) list * tyR
  | Check of ((Var.t * tyR) list) * tmR * tyR option
  | Decl of Var.t * (Var.t * tyR) list * tmR * tyR option
  | Set of string * string

type prog = cmd list

val exec : prog -> unit
