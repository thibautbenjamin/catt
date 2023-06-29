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

let rec tm_apply_sub tm s =
  match tm with
  | Var v -> List.assoc v s
  | Coh(ps,ty,s1) -> Coh (ps,ty, sub_ps_apply_sub s1 s)
and sub_ps_apply_sub s1 s2 = List.map (fun t -> tm_apply_sub t s2) s1

let rec ty_apply_sub ty s =
  match ty with
  | Obj -> Obj
  | Arr(a,u,v) -> Arr(ty_apply_sub a s, tm_apply_sub u s, tm_apply_sub v s)

let sub_apply_sub s1 s2 = List.map (fun (v,t) -> (v,tm_apply_sub t s2)) s1

(* rename is applying a variable to de Bruijn levels substitutions *)
let rec rename_tm tm l =
  match tm with
  | Var v -> Var (Db (List.assoc v l))
  | Coh (ps, ty, sub) -> Coh (ps, ty, rename_sub_ps sub l)
and rename_sub_ps s l =
  List.map (fun tm -> rename_tm tm l) s

let rec rename_ty ty l =
  match ty with
  | Obj -> Obj
  | Arr(a,u,v) -> Arr (rename_ty a l, rename_tm u l, rename_tm v l)

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
