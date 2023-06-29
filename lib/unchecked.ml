open Variables

exception Not_Equal
exception DoubleDef

type ps = Br of ps list

type ty =
  | Obj
  | Arr of ty * tm * tm
and tm =
  | Var of var
  | Coh of ps * ty * sub_ps
and sub_ps = tm list

type ctx = (var * ty) list

type sub = (var * tm) list

let rec ps_to_string = function
  | Br l -> Printf.sprintf "[%s]"
              (List.fold_left (fun s ps -> Printf.sprintf "%s%s" s (ps_to_string ps)) "" l)

let rec ty_to_string = function
  | Obj -> "*"
  | Arr (a,u,v) -> Printf.sprintf "%s | %s -> %s" (ty_to_string a) (tm_to_string u) (tm_to_string v)
and tm_to_string = function
  | Var v -> string_of_var v
  | Coh (ps,ty,s) -> Printf.sprintf "coh(%s,%s)[%s]" (ps_to_string ps) (ty_to_string ty) (ps_sub_to_string s)
and ps_sub_to_string s =
  List.fold_left (fun str t -> Printf.sprintf "%s %s" str (tm_to_string t)) "" s

let rec ctx_to_string = function
  | [] -> ""
  | (x,t)::c -> Printf.sprintf "%s (%s: %s)" (ctx_to_string c) (string_of_var x) (ty_to_string t)

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

let rec tm_do_on_variables tm f =
  match tm with
  | Var v -> (f v)
  | Coh(ps,ty,s) -> Coh (ps,ty, sub_ps_do_on_variables s f)
and sub_ps_do_on_variables s f = List.map (fun t -> tm_do_on_variables t f) s


let rec ty_do_on_variables ty f =
  match ty with
  | Obj -> Obj
  | Arr(a,u,v) -> Arr(ty_do_on_variables a f, tm_do_on_variables u f, tm_do_on_variables v f)

let apply_sub_fn s = fun v -> List.assoc v s

let tm_apply_sub tm s = tm_do_on_variables tm (apply_sub_fn s)
let ty_apply_sub ty s = ty_do_on_variables ty (apply_sub_fn s)

let sub_apply_sub s1 s2 = List.map (fun (v,t) -> (v,tm_apply_sub t s2)) s1

(* rename is applying a variable to de Bruijn levels substitutions *)
let rename_ty ty l = ty_do_on_variables ty (fun v -> Var (Db (List.assoc v l)))

let rec db_levels c =
    match c with
    | [] -> [], [], -1
    | (x,t)::c ->
       let c,l,max = db_levels c in
       if List.mem_assoc x l then
         raise DoubleDef
       else
         let lvl = max + 1 in
         (Db lvl, rename_ty t l) ::c, (x, lvl)::l, lvl

let increase_lv_var v i m =
  match v with
  | Db j -> if  j == 0 then Db (i) else Db (j + m)
  | Name _ | New _ -> assert false
let increase_lv_ty ty i m = ty_do_on_variables ty (fun v -> Var (increase_lv_var v i m))

let suspend_var = function
  | Db i -> Db (i+2)
  | Name _ | New _ as v -> v

let rec suspend_ty = function
  | Obj -> Arr(Obj, Var (Db 0), Var (Db 1))
  | Arr(a,v,u) -> Arr(suspend_ty a, suspend_tm v, suspend_tm u)
and suspend_tm = function
  | Var v -> Var (suspend_var v)
  | Coh _ -> assert false

let rec suspend_ctx : ctx -> ctx = function
  | [] -> (Db 1, Obj) :: (Db 0, Obj) :: []
  | (v,t)::c -> (suspend_var v, suspend_ty t) :: (suspend_ctx c)

let rec ps_to_ctx_aux ps =
  match ps with
  | Br [] -> [(Db 0), Obj], 0, 0
  | Br l -> ps_concat (List.map
                         (fun ps -> let ps,_,m = ps_to_ctx_aux ps in (suspend_ctx ps, 1, m+2))
                         l)
and ps_concat = function
  | [] -> assert false
  | ps :: [] -> ps
  | ps :: l -> ps_glue (ps_concat l) ps
and ps_glue (p1,t1,m1) (p2,t2,m2) =
  List.append (chop_and_increase p2 t1 m1) p1, t2+m1, m1+m2
and chop_and_increase ctx i m =
  match ctx with
  | [] -> assert false
  | _ :: [] -> []
  | (v,t) :: ctx ->
     let v = increase_lv_var v i m in
     let t = increase_lv_ty t i m in
     let ctx = chop_and_increase ctx i m in
     (v,t)::ctx

let ps_to_ctx ps = let c,_,_ = ps_to_ctx_aux ps in c
