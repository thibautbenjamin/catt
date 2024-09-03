open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

let phase = ref (fun _ -> Error.fatal "Uninitialised forward reference")
let cone_comp_n0n = ref (fun _ -> Error.fatal "Uninitialised forward reference")

let rec primary_seq n i =
  match n, i mod 2 with
  | 0, _ -> 1
  | _, 0 -> n+1
  | _, _ -> primary_seq (n-1) (i/2)

let rec secondary_seq n i =
  match n, i mod 2 with
  | 0, _ -> 1
  | _, 0 -> (i/2)+1
  | _, _ -> secondary_seq (n-1) (i/2)

(*
let primary_list n = List.init ((1 lsl (n+1))-1) (primary_seq n)
let secondary_list n = List.init ((1 lsl (n+1))-1) (secondary_seq n)
*)

let cone_coh c l p =
  (* Sanity check: c is non-inv *)
  assert (not (Coh.is_inv c));
  let ps,_,_ = Coh.forget c in
  let d = Unchecked.dim_ps ps in
  let test = Functorialisation.whisk 0 (d-1) (d-1) in
  let testps,_,_ = Coh.forget test in
  (* Sanity check: c is an d0d composite *)
  let _ = Unchecked.check_equal_ps ps testps in
  let ctx = Unchecked.ps_to_ctx ps in
  let maxvars = List.filter (fun v -> snd (snd v)) ctx in
  let f,(fty,_) = List.hd (List.tl maxvars) in
  let g,(gty,_) = List.hd maxvars in
  let res,_ = !cone_comp_n0n (d-1) ((Var(f)),fty) ((Var(g)),gty) l p in
  res

let rec cone_src t ty ty' l p =
  match ty' with
  | Meta_ty(_) -> assert false
  | Obj -> t,ty
  | Arr(b,u,_) ->
    begin
      let inner = cone_src t ty b l p in
      let ucone_ty = cone_ty u b l p in
      let ucone = cone_tm u l p in
      let d' = Unchecked.dim_ty (ucone_ty) in
      Functorialisation.wcomp (ucone,ucone_ty) (d'-1) inner
    end
and cone_ty t ty l p =
  match ty with
  | Meta_ty(_) -> assert false
  | Obj -> Arr(Obj,Var(p),t)
  | Arr(b,_,v) ->
    begin
      let bcone = cone_ty v b l p in
      let vcone = cone_tm v l p in
      let ucone,_ = cone_src t ty ty l p in
      Arr(bcone,vcone,ucone)
    end
and cone_tm t l p =
  match t with
  | Var(v) -> Var(List.assoc v l)
  | Coh(c,s_ps) ->
    begin
      let ps,_,_ = Coh.forget c in
      let ctx = Unchecked.ps_to_ctx ps in
      let _,(l',p') = cone_ctx ctx in
      let c_coned = cone_coh c l' p' in
      let s = Unchecked.sub_ps_to_sub s_ps in
      let s_coned = cone_sub s l' l p' p in
      Unchecked.tm_apply_sub c_coned s_coned
    end
  | Meta_tm(_) -> assert false
and cone_ctx c =
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
  let tctx,pairs = aux c point in
  let res = List.append tctx ((point,(Obj,false))::c) in
  res,(pairs,point)
and cone_sub s l1 l2 p1 p2 =
  let s = List.map (fun x -> (x,Hashtbl.find s.tbl x)) s.vars in
  let rec aux s =
    match s with
    | [] -> []
    | (v,t)::tl ->
      let tcone = cone_tm t l2 p2 in
      (List.assoc v l1, tcone)::(aux tl)
  in Unchecked.alist_to_sub (List.append (aux s) ((p1,Var(p2))::s))

let cone_tmty (t,ty) l p =
  let tc = cone_tm t l p in
  let tcty = cone_ty t ty l p in
  (tc,tcty)

let cones_postprocess_fn c t =
  let tm = check_term (Ctx.check c) t in
  let ty = Ty.forget (Tm.typ tm) in
  let cctx,(pairs,p) = cone_ctx c in
  let cty = cone_ty t ty pairs p in
  let ct = cone_tm t pairs p in
  let _ = Printf.printf "Checking: %s of type %s in context %s\n%!"
    (Unchecked.tm_to_string ct)
    (Unchecked.ty_to_string cty)
    (Unchecked.ctx_to_string cctx) in
  let _ = check_term (Ctx.check cctx) ct in
  (*
  let _ = check_term (Ctx.check cctx) ~ty:cty ct in
  *)
  cctx, ct
