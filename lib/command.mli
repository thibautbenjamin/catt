open Common
open Kernel
open Raw_types
open Unchecked_types.Unchecked_types(Coh)

type cmd =
  | Coh of Var.t * (Var.t * tyR) list * tyR
  | Check of (Var.t * tyR) list * tmR * tyR option
  | Decl of Var.t * (Var.t * tyR) list * tmR * tyR option
  | Set of string * string

type prog = cmd list

val postprocess_fn : (ctx -> tm -> ctx * tm) ref
val exec : loop_fn:(unit -> unit) -> prog -> unit
