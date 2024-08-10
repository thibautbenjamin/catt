open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

let rec cone_src t ty ty' l p =
  let d = Unchecked.dim_ty ty in
  match ty' with
  | Meta_ty(_) -> assert false
  | Obj -> t,ty
  | Arr(b,u,_) ->
    begin
      let inner, inner_ty = cone_src t ty b l p in
      let ucone_ty = cone_ty u b l p in
      let ucone = cone_tm u l p in
      let d' = Unchecked.dim_ty ucone_ty in
      let whisk = Functorialisation.whisk (d'-1) 0 (d-d') in
      let _,whisk_ty,_ = Coh.forget whisk in
      let whisk_sub_ps = Functorialisation.whisk_sub_ps (d-d') ucone ucone_ty inner inner_ty in
      let whisk_sub = Unchecked.sub_ps_to_sub whisk_sub_ps in
      Coh(whisk,whisk_sub_ps), Unchecked.ty_apply_sub whisk_ty whisk_sub
    end
and cone_ty t ty l p =
  match ty with
  | Meta_ty(_) -> assert false
  | Obj -> Arr(Obj,p,t)
  | Arr(b,_,v) ->
    begin
      let bcone = cone_ty v b l p in
      let vcone = cone_tm v l p in
      let ucone,_ = cone_src t ty ty l p in
      Arr(bcone,vcone,ucone)
    end
and cone_tm t l _p =
  match t with
  | Var(v) -> Var(List.assoc v l)
  | Coh(_c,_s) -> assert false
  | Meta_tm(_) -> assert false

let cone_ctx c =
  let rec aux c p =
    match c with
    | [] -> [],[]
    | (t,(ty,e))::tl ->
    begin
      let c,pairs = aux tl p in
      let tilde = Var.fresh() in
      (tilde,(cone_ty (Var(t)) ty pairs p,e))::c,
      (t,tilde)::pairs
    end in
  let point = Var.fresh() in
  let tctx,pairs = aux c (Var(point)) in
  let res = List.concat [tctx;(point,(Obj,false))::c] in
  res,(pairs,point)

let cone_sub s l p1 p2 =
  let rec aux s =
    match s with
    | [] -> []
    | (v,t)::tl ->
      let tcone = cone_tm t l (Var(p2)) in
      (List.assoc v l, tcone)::(aux tl)
  in List.concat [aux s;(p1,Var(p2))::s]

let cones_postprocess_fn c t =
  let tm = check_term (Ctx.check c) t in
  let ty = Ty.forget (Tm.typ tm) in
  let cctx,(pairs,p) = cone_ctx c in
  let cty = cone_ty t ty pairs (Var(p)) in
  let ct = cone_tm t pairs (Var(p)) in
  let _ = Printf.printf "Checking: %s of type %s in context %s\n%!"
    (Unchecked.tm_to_string ct)
    (Unchecked.ty_to_string cty)
    (Unchecked.ctx_to_string cctx) in
  let _ = check_term (Ctx.check cctx) ~ty:cty ct in
  cctx, ct
