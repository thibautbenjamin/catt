open Common

type cmd =
  | Coh of Var.t * (Var.t * Syntax.ty) list * Syntax.ty
  | Check of ((Var.t * Syntax.ty) list) * Syntax.tm * Syntax.ty option
  | Decl of Var.t * (Var.t * Syntax.ty) list * Syntax.tm * Syntax.ty option

type prog = cmd list

val exec : prog -> unit
