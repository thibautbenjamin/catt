open Common

exception DoubleDef

let rec ps_to_string = function
  | Br l -> Printf.sprintf "[%s]"
              (List.fold_left
                 (fun s ps -> Printf.sprintf "%s%s" (ps_to_string ps) s)
                 ""
                 l)

let rec ty_to_string = function
  | Meta_ty i -> Printf.sprintf "_ty%i" i
  | Obj -> "*"
  | Arr (a,u,v) ->
    Printf.sprintf "%s | %s -> %s"
      (ty_to_string a)
      (tm_to_string u)
      (tm_to_string v)
and tm_to_string = function
  | Var v -> Var.to_string v
  | Meta_tm i -> Printf.sprintf "_tm%i" i
  | Coh (ps,ty,s) ->
    Printf.sprintf "coh(%s,%s)[%s]"
      (ps_to_string ps)
      (ty_to_string ty)
      (sub_ps_to_string s)
and sub_ps_to_string = function
  | [] -> ""
  | t::s -> Printf.sprintf "%s %s" (sub_ps_to_string s)  (tm_to_string t)

let rec ctx_to_string = function
  | [] -> ""
  | (x,(t,true))::c ->
    Printf.sprintf "%s (%s: %s)"
      (ctx_to_string c)
      (Var.to_string x)
      (ty_to_string t)
  | (x,(t,false))::c ->
    Printf.sprintf "%s {%s: %s}"
      (ctx_to_string c)
      (Var.to_string x)
      (ty_to_string t)

let rec sub_to_string = function
  | [] -> ""
  | (x,t)::s ->
    Printf.sprintf "%s (%s: %s)"
      (sub_to_string s)
      (Var.to_string x)
      (tm_to_string t)

let rec meta_ctx_to_string = function
  | [] -> ""
  | (i,t)::c ->
    Printf.sprintf "%s (_tm%i: %s)"
      (meta_ctx_to_string c)
      i
      (ty_to_string t)

let rec check_equal_ps ps1 ps2 =
  match ps1, ps2 with
  | Br [], Br[] -> ()
  | Br (ps1::l1), Br(ps2::l2) ->
     check_equal_ps ps1 ps2;
     List.iter2 check_equal_ps l1 l2
  | Br[], Br (_::_) | Br(_::_), Br[] ->
    raise (Error.NotEqual (ps_to_string ps1, ps_to_string ps2))

let rec check_equal_ty ty1 ty2 =
  match ty1, ty2 with
  | Meta_ty i, Meta_ty j ->
    if i <> j then raise (Error.NotEqual(string_of_int i, string_of_int j))
  | Obj, Obj -> ()
  | Arr(ty1, u1, v1), Arr(ty2, u2, v2) ->
     check_equal_ty ty1 ty2;
     check_equal_tm u1 u2;
     check_equal_tm v1 v2
  | Obj, Arr _ | Arr _, Obj
  | Meta_ty _, Obj | Meta_ty _, Arr _
  | Obj, Meta_ty _ | Arr _, Meta_ty _ ->
    raise (Error.NotEqual (ty_to_string ty1, ty_to_string ty2))
and check_equal_tm tm1 tm2 =
  match tm1, tm2 with
  | Var v1, Var v2 -> Var.check_equal v1 v2
  | Meta_tm i, Meta_tm j ->
    if i <> j then raise (Error.NotEqual(string_of_int i, string_of_int j))
  | Coh(ps1, ty1, s1), Coh(ps2, ty2, s2) ->
     check_equal_ps ps1 ps2;
     check_equal_ty ty1 ty2;
     check_equal_sub_ps s1 s2
  | Var _, Coh _ | Coh _, Var _
  | Meta_tm _, Var _| Meta_tm _, Coh _
  | Var _, Meta_tm _ | Coh _, Meta_tm _ ->
    raise (Error.NotEqual (tm_to_string tm1, tm_to_string tm2))
and check_equal_sub_ps s1 s2 =
  List.iter2 check_equal_tm s1 s2

let rec check_equal_ctx ctx1 ctx2 =
  match ctx1, ctx2 with
  | [], [] -> ()
  | (v1,(t1,_))::c1, (v2,(t2,_))::c2 ->
     Var.check_equal v1 v2;
     check_equal_ty t1 t2;
     check_equal_ctx c1 c2
  | _::_,[] | [],_::_ ->
    raise (Error.NotEqual (ctx_to_string ctx1, ctx_to_string ctx2))

let rec tm_do_on_variables tm f =
  match tm with
  | Var v -> (f v)
  | Meta_tm i -> Meta_tm i
  | Coh(ps,ty,s) -> Coh (ps,ty, sub_ps_do_on_variables s f)
and sub_ps_do_on_variables s f = List.map (fun t -> tm_do_on_variables t f) s

let rec ty_do_on_variables ty f =
  match ty with
  | Meta_ty i -> Meta_ty i
  | Obj -> Obj
  | Arr(a,u,v) ->
    Arr(ty_do_on_variables a f, tm_do_on_variables u f, tm_do_on_variables v f)

let var_apply_sub v s = List.assoc v s
let tm_apply_sub tm s = tm_do_on_variables tm (fun v -> var_apply_sub v s)
let ty_apply_sub ty s = ty_do_on_variables ty (fun v -> var_apply_sub v s)
let sub_apply_sub s1 s2 = List.map (fun (v,t) -> (v,tm_apply_sub t s2)) s1

(* rename is applying a variable to de Bruijn levels substitutions *)
let rename_ty ty l = ty_do_on_variables ty (fun v -> Var (Db (List.assoc v l)))

let rec db_levels c =
    match c with
    | [] -> [], [], -1
    | (x,(t,expl))::c ->
       let c,l,max = db_levels c in
       if List.mem_assoc x l then
         raise DoubleDef
       else
         let lvl = max + 1 in
         (Var.Db lvl, (rename_ty t l, expl)) ::c, (x, lvl)::l, lvl

let increase_lv_ty ty i m =
  ty_do_on_variables ty (fun v -> Var (Var.increase_lv v i m))

let ps_to_ctx ps =
  let rec ps_to_ctx_aux ps =
    match ps with
    | Br [] -> [(Var.Db 0), (Obj, true)], 0, 0
    | Br l ->
      ps_concat (List.map
                   (fun ps ->
                      let ps,_,m = ps_to_ctx_aux ps in
                      (Suspension.ctx (Some 1) ps, 1, m+2))
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
    | (v,(t,expl)) :: ctx ->
      let v = Var.increase_lv v i m in
      let t = increase_lv_ty t i m in
      let ctx = chop_and_increase ctx i m in
      (v,(t,expl))::ctx
  in
  let c,_,_ = ps_to_ctx_aux ps in c

let sub_ps_to_sub s ps =
  let ps = ps_to_ctx ps in
  List.map2 (fun t (x,_) -> (x,t)) s ps, ps
