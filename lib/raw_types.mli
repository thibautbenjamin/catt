open Common

type builtin = Comp | Id

type tyR = Letin_ty of Var.t * tmR * tyR | ObjR | ArrR of tmR * tmR

and tmR =
  | Letin_tm of Var.t * tmR * tmR
  | VarR of Var.t
  | BuiltinR of builtin
  | Sub of tmR * subR * int option * bool
  | Meta
  | Op of int list * tmR
  | Inverse of tmR
  | Unit of tmR

and subR = (tmR * int) list
