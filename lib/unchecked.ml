open Variables

exception Not_Equal

type ps = Br of ps list

type ty =
  | Obj
  | Arr of ty * tm * tm
and tm =
  | Var of var
  | Coh of ps * ty * sub_ps
and sub_ps = tm list

type ctx = (var * ty) list

let rec check_equal_ps ps1 ps2 =
  match ps1, ps2 with
  | Br [], Br[] -> ()
  | Br (ps1::l1), Br(ps2::l2) ->
     check_equal_ps ps1 ps2;
     List.iter2 check_equal_ps l1 l2
  | Br[], Br (_::_) | Br(_::_), Br[] -> raise Not_Equal

let rec check_equal_ty ty1 ty2 =
  match ty1, ty2 with
  | Obj, Obj -> ()
  | Arr(ty1, u1, v1), Arr(ty2, u2, v2) ->
     check_equal_ty ty1 ty2;
     check_equal_tm u1 u2;
     check_equal_tm v1 v2
  | Obj, Arr _ | Arr _, Obj -> raise Not_Equal
and check_equal_tm tm1 tm2 =
  match tm1, tm2 with
  | Var v1, Var v2 -> if v1 != v2 then raise Not_Equal
  | Coh(ps1, ty1, s1), Coh(ps2, ty2, s2) ->
     check_equal_ps ps1 ps2;
     check_equal_ty ty1 ty2;
     check_equal_sub_ps s1 s2
  | Var _, Coh _ | Coh _, Var _ -> raise Not_Equal
and check_equal_sub_ps s1 s2 =
  List.iter2 check_equal_tm s1 s2
