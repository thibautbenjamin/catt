open Kernel

type tyR =
  | Letin_ty of Var.t * tmR * tyR
  | ObjR
  | ArrR of tmR * tmR
and tmR =
  | Letin_tm of Var.t * tmR * tmR
  | VarR of Var.t
  | Sub of tmR * (tmR * bool) list * int option
  | Meta
