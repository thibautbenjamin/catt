type ps = Br of ps list

type ty =
  | Obj
  | Arr of ty * tm * tm
and tm =
  | Var of Var.t
  | Coh of ps * ty * sub_ps
and sub_ps = tm list

type ctx = (Var.t * ty) list

type sub = (Var.t * tm) list
