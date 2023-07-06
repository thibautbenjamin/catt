open Common

let ps ps = Br [ps]

let rec ty = function
  | Obj -> Arr(Obj, Var (Db 0), Var (Db 1))
  | Arr(a,v,u) -> Arr(ty a, tm v, tm u)
  | Meta_ty _ -> assert false
and tm = function
  | Var v -> Var (Var.suspend v)
  | Coh (p,t,s) -> Coh(ps p, ty t, sub_ps s)
  | Meta_tm _ -> assert false
and sub_ps = function
  | [] -> [Var (Var.Db 1); Var (Var.Db 0)]
  | t::s -> (tm t) :: (sub_ps s)

let rec ctx = function
  | [] -> (Var.Db 1, (Obj, false)) :: (Var.Db 0, (Obj, false)) :: []
  | (v,(t,expl))::c -> (Var.suspend v, (ty t, expl)) :: (ctx c)

let rec iter_n_times n f base =
  if n = 0 then base else f (iter_n_times (n-1) f base)

let iter_option f n base =
  match n with
  | None -> base
  | Some n -> iter_n_times n f base

let ps = iter_option ps
let ty = iter_option ty
let tm = iter_option tm
let sub_ps = iter_option sub_ps
let ctx = iter_option ctx