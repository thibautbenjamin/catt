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
  | CoindDef of
      Var.t * (Var.t * tyR) list * tmR * tmR * tmR * tmR * tmR * tmR * tmR
  | RecDef of
      Var.t * (Var.t * tyR) list * tmR * tmR * tmR * tmR * tmR * tmR * tmR

type prog = cmd list

val postprocess_fn : (ctx -> tm -> ctx * tm) ref
val exec : loop_fn:(unit -> unit) -> prog -> unit
