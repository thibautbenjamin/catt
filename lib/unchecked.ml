open Common
open Unchecked_types

module Unchecked (Coh : sig type t end) =
struct
  open Unchecked_types(Coh)

  module Make
      (Coh : sig
         val forget : Coh.t -> ps * Unchecked_types(Coh).ty * coh_pp_data
         val to_string : Coh.t -> string
         val func_data : Coh.t -> functorialisation_data option
         val check_equal : Coh.t -> Coh.t -> unit
         val check : ps -> ty -> coh_pp_data -> Coh.t
       end)
  = struct

    exception NotInImage

    let rec func_to_string = function
      | [] -> ""
      | i::func -> Printf.sprintf "%s%d" (func_to_string func) i

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
        if !Settings.verbosity >= 3 then
          Printf.sprintf "%s | %s -> %s"
            (ty_to_string a)
            (tm_to_string u)
            (tm_to_string v)
        else
          Printf.sprintf "%s -> %s"
            (tm_to_string u)
            (tm_to_string v)
    and tm_to_string = function
      | Var v -> Var.to_string v
      | Meta_tm i -> Printf.sprintf "_tm%i" i
      | Coh (c,s) ->
        if not (!Settings.unroll_coherences) then
          let func = Coh.func_data c in
          Printf.sprintf "(%s%s)"
            (Coh.to_string c)
            (sub_ps_to_string ?func s)
        else
          Printf.sprintf "%s[%s]"
            (Coh.to_string c)
            (sub_ps_to_string s)
    and sub_ps_to_string ?func s =
      match func with
      | None ->
        begin
          match s with
          | [] -> ""
          | (t,expl)::s ->
            if(expl || !Settings.print_explicit_substitutions) then
              Printf.sprintf "%s %s" (sub_ps_to_string s)  (tm_to_string t)
            else sub_ps_to_string s
        end
      | Some func ->
        match s,func with
        | [],[] -> ""
        | (t,true)::s, i::func ->
          Printf.sprintf "%s %s"
            (sub_ps_to_string ~func s)
            (bracket i (tm_to_string t))
        | (t,false)::s, func ->
          if(!Settings.print_explicit_substitutions) then
            Printf.sprintf "%s %s" (sub_ps_to_string ~func s) (tm_to_string t)
          else sub_ps_to_string ~func s
        | _::_,[] | [], _::_ ->
          Error.fatal "Wrong number of functorialisation arguments"
    and coh_pp_data_to_string ?(print_func=false) (name, susp, func) =
      let susp_name =
        if susp > 0 then Printf.sprintf "!%i%s" susp name else name
      in
      if print_func
      then
        match func with
        | None -> susp_name
        | Some func -> let func = func_to_string func in susp_name^"/"^func
      else susp_name
    and bracket i s =
      if i <= 0 then s else Printf.sprintf "[%s]" (bracket (i-1) s)

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
      raise (NotEqual (ps_to_string ps1, ps_to_string ps2))

  let rec check_equal_ty ty1 ty2 =
    match ty1, ty2 with
    | Meta_ty i, Meta_ty j ->
      if i <> j then raise (NotEqual(string_of_int i, string_of_int j))
    | Obj, Obj -> ()
    | Arr(ty1, u1, v1), Arr(ty2, u2, v2) ->
      check_equal_ty ty1 ty2;
      check_equal_tm u1 u2;
      check_equal_tm v1 v2
    | Obj, Arr _ | Arr _, Obj
    | Meta_ty _, Obj | Meta_ty _, Arr _
    | Obj, Meta_ty _ | Arr _, Meta_ty _ ->
      raise (NotEqual (ty_to_string ty1, ty_to_string ty2))
  and check_equal_tm tm1 tm2 =
    match tm1, tm2 with
    | Var v1, Var v2 -> Var.check_equal v1 v2
    | Meta_tm i, Meta_tm j ->
      if i <> j then raise (NotEqual(string_of_int i, string_of_int j))
    | Coh(coh1, s1), Coh(coh2, s2) ->
      Coh.check_equal coh1 coh2;
      check_equal_sub_ps s1 s2
    | Var _, Coh _ | Coh _, Var _
    | Meta_tm _, Var _| Meta_tm _, Coh _
    | Var _, Meta_tm _ | Coh _, Meta_tm _ ->
      raise (NotEqual (tm_to_string tm1, tm_to_string tm2))
  and check_equal_sub_ps s1 s2 =
    List.iter2 (fun (t1,_) (t2,_) -> check_equal_tm t1 t2) s1 s2

  let rec check_equal_ctx ctx1 ctx2 =
    match ctx1, ctx2 with
    | [], [] -> ()
    | (v1,(t1,_))::c1, (v2,(t2,_))::c2 ->
      Var.check_equal v1 v2;
      check_equal_ty t1 t2;
      check_equal_ctx c1 c2
    | _::_,[] | [],_::_ ->
      raise (NotEqual (ctx_to_string ctx1, ctx_to_string ctx2))

  let rec tm_do_on_variables tm f =
    match tm with
    | Var v -> (f v)
    | Meta_tm i -> Meta_tm i
    | Coh(c,s) -> Coh (c, sub_ps_do_on_variables s f)
  and sub_ps_do_on_variables s f = List.map (fun (t,expl) -> tm_do_on_variables t f, expl) s

  let rec ty_do_on_variables ty f =
    match ty with
    | Meta_ty i -> Meta_ty i
    | Obj -> Obj
    | Arr(a,u,v) ->
      Arr(ty_do_on_variables a f, tm_do_on_variables u f, tm_do_on_variables v f)

  let var_apply_sub v s =
    match List.assoc_opt v s with
    | Some t -> t
    | None -> Var v
  let tm_apply_sub tm s = tm_do_on_variables tm (fun v -> var_apply_sub v s)
  let ty_apply_sub ty s = ty_do_on_variables ty (fun v -> var_apply_sub v s)
  let _sub_apply_sub s1 s2 = List.map (fun (v,t) -> (v,tm_apply_sub t s2)) s1

  let rec var_sub_preimage v s =
    match s with
    | [] -> raise NotInImage
    | (w, Var v')::_ when v = v' -> Var w
    | _::s -> var_sub_preimage v s
  let tm_sub_preimage tm s = tm_do_on_variables tm
      (fun v -> var_sub_preimage v s)

  (* rename is applying a variable to de Bruijn levels substitutions *)
  let rename_ty ty l = ty_do_on_variables ty
      (fun v -> Var (Db (List.assoc v l)))

  let rec db_levels c =
    match c with
    | [] -> [], [], -1
    | (x,(t,expl))::c ->
      let c,l,max = db_levels c in
      if List.mem_assoc x l then
        raise (DoubledVar(Var.to_string x))
      else
        let lvl = max + 1 in
        (Var.Db lvl, (rename_ty t l, expl)) ::c, (x, lvl)::l, lvl

  let increase_lv_ty ty i m =
    ty_do_on_variables ty (fun v -> Var (Var.increase_lv v i m))

  let suspend_ps ps = Br [ps]

  let rec suspend_ty = function
    | Obj -> Arr(Obj, Var (Db 0), Var (Db 1))
    | Arr(a,v,u) -> Arr(suspend_ty a, suspend_tm v, suspend_tm u)
    | Meta_ty _ -> Error.fatal "meta-variables should be resolved"
  and suspend_tm = function
    | Var v -> Var (Var.suspend v)
    | Coh (c,s) -> Coh(suspend_coh c, suspend_sub_ps s)
    | Meta_tm _ -> Error.fatal "meta-variables should be resolved"
  and suspend_coh c =
    let p,t,(name,susp,f) = Coh.forget c in
    Coh.check (suspend_ps p) (suspend_ty t) (name, susp+1, f)
  and suspend_sub_ps = function
    | [] -> [Var (Var.Db 1), false; Var (Var.Db 0), false]
    | (t,expl)::s -> (suspend_tm t, expl) :: (suspend_sub_ps s)

  let rec suspend_ctx = function
    | [] -> (Var.Db 1, (Obj, false)) :: (Var.Db 0, (Obj, false)) :: []
    | (v,(t,expl))::c -> (Var.suspend v, (suspend_ty t, expl)) :: (suspend_ctx c)

  let ps_to_ctx ps =
    let rec ps_to_ctx_aux ps =
      match ps with
      | Br [] -> [(Var.Db 0), (Obj, true)], 0, 0
      | Br l ->
        ps_concat (List.map
                     (fun ps ->
                        let ps,_,m = ps_to_ctx_aux ps in
                        (suspend_ctx  ps, 1, m+2))
                     l)
    and ps_concat = function
      | [] -> Error.fatal "empty is not a pasting scheme"
      | ps :: [] -> ps
      | ps :: l -> ps_glue (ps_concat l) ps
    and ps_glue (p1,t1,m1) (p2,t2,m2) =
      List.append (chop_and_increase p2 t1 m1) p1, t2+m1, m1+m2
    and chop_and_increase ctx i m =
      match ctx with
      | [] -> Error.fatal "empty is not a pasting scheme"
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
    try List.map2 (fun (t,_) (x,_) -> (x,t)) s ps, ps
    with Invalid_argument _ -> Error.fatal "uncaught wrong number of arguments"

  let max_fresh_var c =
    let rec find_max c i =
      match c with
      | [] -> i
      | (Var.New j, _) :: c when j >= i -> find_max c j
      | ((Var.Name _ | Var.Db _ | Var.New _ ), _) :: c  -> find_max c i
    in
    find_max c 0

  let two_fresh_vars c =
    let i = max_fresh_var c in
    Var.New (i+1), Var.New (i+2)

  let rec identity_ps = function
    | [] -> []
    | (x,(_,expl))::c -> (Var x,expl) :: (identity_ps c)

  let rec tm_contains_var t x =
    match t with
    | Var v -> v = x
    | Coh(_,s) -> List.exists (fun (t,_) -> tm_contains_var t x) s
    | Meta_tm _ -> Error.fatal "meta-variables should be resolved"

  let tm_contains_vars t l =
    List.exists (tm_contains_var t) l

  let rec dim_ty = function
    | Obj -> 0
    | Arr(a,_,_) -> 1 + dim_ty a
    | Meta_ty _ -> Error.fatal "meta-variables should be resolved"

  let rec dim_ctx = function
    | [] -> 0
    | (_,(t,_))::c -> max (dim_ctx c) (dim_ty t)

  let rec dim_ps = function
    | Br [] -> 0
    | Br l -> 1 + max_list_ps l
  and max_list_ps = function
    | [] -> 0
    | p::l -> max (dim_ps p) (max_list_ps l)

end
end
