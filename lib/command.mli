open Common
open Kernel
open Raw_types
open Unchecked_types.Unchecked_types(Coh)(Tm)

type cmd =
  | Coh of Var.t * (Var.t * tyR) list * tyR
  | Check of (Var.t * tyR) list * tmR * tyR option
  | Check_builtin of builtin
  | Decl of Var.t * (Var.t * tyR) list * tmR * tyR option
  | Decl_builtin of Var.t * builtin
  | Set of string * string
  | Benchmark of (Var.t * tyR) list * tmR
  | Benchmark_builtin of builtin

type prog = cmd list

val postprocess_fn : (ctx -> tm -> ctx * tm) ref
val exec : loop_fn:(unit -> unit) -> prog -> unit
