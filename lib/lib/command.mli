open Common
open Raw_types

type theory_setting = Invertibility of string

type cmd =
  | Coh of Var.t * (Var.t * tyR) list * tyR
  | Check of (Var.t * tyR) list * tmR * tyR option
  | Check_builtin of builtin
  | Decl of Var.t * (Var.t * tyR) list * tmR * tyR option
  | Decl_builtin of Var.t * builtin
  | Set of string * string
  | SetTheory of theory_setting
  | Benchmark of (Var.t * tyR) list * tmR
  | Benchmark_builtin of builtin

type prog = cmd list

val exec : ?theory:theory -> loop_fn:(unit -> unit) -> prog -> unit
