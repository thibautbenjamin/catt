open Std
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
  let sub_ps_apply_sub s1 s2 =
    sub_ps_do_on_variables s1 (fun v -> var_apply_sub v s2)
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


  (* Definition of FreePos(B):
     - in the paper, we define the bipointed verison with suspension and wedge
     - here we don't need the left point, as it is always the DeBruijn level 0,\
     however, we need the right point. We also need to rename every variable in\
     the right of a wedge, to avoid name clashes. To help with this, we also \
     carry around the maximal variable of a context. Given a function f, f_rp\
     is the name of the rightpointed variant, giving the right point and the\
     maximal variable.
  *)

  type ctx_bp = {ctx: ctx; max: int; rp: int}
  type sub_ps_bp = {sub_ps: sub_ps; l: tm; r: tm}

  let rec suspend_ctx_rp ctx =
    match ctx with
    | [] ->
      let ctx = (Var.Db 1, (Obj, false))::(Var.Db 0, (Obj, false))::[] in
      {ctx; max = 1; rp = 1}
    | (v,(t,expl))::c ->
      let c = suspend_ctx_rp c in
      let v = Var.suspend v in
      match v with
      | Var.Db i ->
        {ctx = (v, (suspend_ty t, expl))::c.ctx; max = max i c.max; rp = c.rp;}
      | _ ->
        {ctx = (v, (suspend_ty t, expl))::c.ctx; max = c.max; rp = c.rp}

  let suspend_ctx ctx =
    (suspend_ctx_rp ctx).ctx

  let var_inr_wedge v ctx_bp =
    match v with
    | Var.Db j ->
      if  j = 0 then (Var.Db ctx_bp.rp)
      else Var.Db (j + ctx_bp.max)
    | Name _ | New _ -> Error.fatal "expecting a de-bruijn level"

  let ty_inr_wedge ty ctx_bp =
    ty_do_on_variables ty (fun v -> Var (var_inr_wedge v ctx_bp))
  let tm_inr_wedge tm ctx_bp =
    tm_do_on_variables tm (fun v -> Var (var_inr_wedge v ctx_bp))

  let rec ps_to_ctx_rp ps =
    match ps with
    | Br [] -> {ctx = [(Var.Db 0), (Obj, true)]; rp = 0; max = 0}
    | Br l -> let _,ctx = canonical_inclusions l in
      ctx
  and canonical_inclusions l =
    match l with
    | [] -> Error.fatal "empty inclusions"
    | [ps] ->
      [suspend_sub_ps (identity_ps ps)], suspend_ctx_rp (ps_to_ctx_rp ps).ctx
    | ps::l ->
      let id = suspend_sub_ps (identity_ps ps) in
      let ctx_ps = suspend_ctx_rp (ps_to_ctx_rp ps).ctx in
      let incls,ctx_base = canonical_inclusions l in
      let ctx_bp =
        {ctx = append_onto_ctx ctx_ps ctx_base;
         rp = ctx_ps.rp + ctx_base.max;
         max = ctx_ps.max + ctx_base.max}
      in
      let incl = List.map (fun (t,e) -> tm_inr_wedge t ctx_base,e) id in
      incl::incls, ctx_bp
  and append_onto_ctx ctx base =
    let rec aux = function
      | [] -> Error.fatal "empty context in wedge"
      | [_] -> base.ctx
      | (v,(t,expl))::ctx ->
        let t = ty_inr_wedge t base in
        let v = var_inr_wedge v base in
        (v,(t,expl))::(aux ctx)
    in aux ctx.ctx
  and identity_ps ps =
    match ps with
    | Br [] -> [Var (Var.Db 0), true]
    | Br l ->
      let incls,_ = canonical_inclusions l in
      wedge_sub_ps incls
  and wedge_sub_ps l = wedge_sub_ps_bp (List.map sub_ps_to_sub_ps_bp l)
  and wedge_sub_ps_bp l =
    let lp = (List.last l).l in
    List.fold_right
      (fun s sub -> List.append s.sub_ps((s.r,false)::sub))
      l
      [lp,false]
  and sub_ps_to_sub_ps_bp sub_ps =
    match sub_ps with
    | [] | [_] -> Error.fatal "bipointed substitution need at least two points"
    | [(r,_);(l,_)] -> {sub_ps = []; l; r}
    | t::s ->
      let s = sub_ps_to_sub_ps_bp s in
      {sub_ps = t::s.sub_ps; l = s.l; r = s.r}

  let canonical_inclusions l = let incls,_ = canonical_inclusions l in incls
  let ps_to_ctx ps = (ps_to_ctx_rp ps).ctx

  let sub_ps_to_sub s ps =
    let ps = ps_to_ctx ps in
    try List.map2 (fun (t,_) (x,_) -> (x,t)) s ps, ps
    with Invalid_argument _ -> Error.fatal "uncaught wrong number of arguments"

  let suspwedge_subs_ps list_subs list_ps =
    let incls = canonical_inclusions list_ps in
    wedge_sub_ps
      (List.map3
         (fun s ps i ->
            sub_ps_apply_sub
              (suspend_sub_ps s)
              (fst (sub_ps_to_sub i (suspend_ps ps))))
         list_subs list_ps incls)

  let opsuspwedge_subs_ps list_subs list_ps =
    let rec swap_bp sub =
      match sub with
      | [] | [_] -> Error.fatal "wedge without two basepoints"
      | [r;l] -> [l;r]
      | t::sub -> t::(swap_bp sub)
    in
    let incls = canonical_inclusions list_ps in
    wedge_sub_ps
      (List.map3
         (fun s ps i ->
            sub_ps_apply_sub
              (swap_bp (suspend_sub_ps s))
              (fst (sub_ps_to_sub i (suspend_ps ps))))
         (List.rev list_subs) (List.rev list_ps) (List.rev incls))

  let max_fresh_var c =
    let rec find_max c i =
      match c with
      | [] -> i
      | (Var.New j, _) :: c when j >= i -> find_max c j
      | ((Var.Name _ | Var.Db _ | Var.New _ ), _) :: c  -> find_max c i
    in
    find_max c 0

  let rec ps_compose i ps1 ps2 =
    match i, ps1, ps2 with
    | 0, Br l1, Br l2 ->
      let i1 = identity_ps (Br l1) in
      let i2 = identity_ps (Br l2) in
      let ctx_bp = ps_to_ctx_rp ps1 in
      let i2 = List.map (fun (x,e) -> tm_inr_wedge x ctx_bp, e) i2 in
      Br (List.append l2 l1),
      i1,
      i2
    | i, Br l1, Br l2 ->
      try
        let list = List.map2 (ps_compose (i-1)) l1 l2 in
        let lps = List.map (fun (x,_,_) -> x) list in
        let li1 = List.map (fun (_,x,_) -> x) list in
        let li2 = List.map (fun (_,_,x) -> x) list in
        Br lps, suspwedge_subs_ps li1 lps, suspwedge_subs_ps li2 lps
      with Invalid_argument _ ->
        Error.fatal "composition of pasting schemes only allowed when their\
                     boundaries match up"

  let rec pullback_up i ps1 ps2 s1 s2 =
    match i, ps1, ps2, s1, s2 with
    | 0,_,_,s1,s2 ->
      let rec append s2 =
        match s2 with
        | [] -> Error.fatal "substitution to pasting scheme cannot be empty"
        | [_] -> s1
        | t::s2 -> t::(append s2)
      in append s2
    | i, Br l1, Br l2, s1, s2 ->
      let incls1 = canonical_inclusions l1 in
      let incls2 = canonical_inclusions l2 in
      let s1,_ = sub_ps_to_sub s1 ps1 in
      let s2,_ = sub_ps_to_sub s2 ps2 in
      let ls =
        List.map4 (fun ps1 ps2 i1 i2 ->
            let s1 = sub_ps_to_sub_ps_bp (sub_ps_apply_sub i1 s1) in
            let s2 = sub_ps_to_sub_ps_bp (sub_ps_apply_sub i2 s2) in
            let hom_sub = pullback_up (i-1) ps1 ps2 s1.sub_ps s2.sub_ps in
            {sub_ps = hom_sub; l = s1.l; r = s1.r})
          l1 l2 incls1 incls2
      in
      wedge_sub_ps_bp ls

  let two_fresh_vars c =
    let i = max_fresh_var c in
    Var.New (i+1), Var.New (i+2)

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

  let rec ty_to_sub_ps a =
    match a with
    | Obj -> []
    | Arr(a,u,v) -> (v,false)::(u,false)::(ty_to_sub_ps a)
    | Meta_ty _ -> Error.fatal "substitution can only be computed after\
                                resolving the type"
end
end
