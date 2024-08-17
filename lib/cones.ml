open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

let phase = ref (fun _ -> Error.fatal "Uninitialised forward reference")

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

let rec tgt n t ty = match n, ty with
  | 0, _ -> t, ty
  | _, Arr(b,_,t) -> tgt (n-1) t b 
  | _, _ -> assert false

(*
  \t{a\s_{0} b} = (\ldots(((\phi^{n}_{1}(\t a, \t b) \s_{k^{(n)}_{1}} \phi
  ^{k^{(n)}_{1}}_{m^{(n)}_{1}+1}(\tgt{k^{(n)}_{1}}(a),\tgt{k^{(n)}_{1}}(b))) \s_{k^{(n)}_{2}} \phi
  ^{k^{(n)}_{2}}_{m^{(n)}_{2}+1}(\tgt{k^{(n)}_{2}}(a),\tgt{k^{(n)}_{2}}(b))) \s_{k^{(n)}_{3}} \phi
  ^{k^{(n)}_{3}}_{m^{(n)}_{3}+1}(\tgt{k^{(n)}_{3}}(a),\tgt{k^{(n)}_{3}}(b)))\ldots) \s_{k^{(n)}_{2^{n}}} \phi
  ^{k^{(n)}_{2^{n}}}_{m^{(n)}_{2^{n}}+1}(\tgt{k^{(n)}_{2^{n}}}(a),\tgt{k^{(n)}_{2^{n}}}(b))
*)
let cone_comp_n0n n f fty g gty l p =
  let d' = Unchecked.dim_ty fty in
  let rec aux k =
    match k with
    | 0 ->
      begin
        !phase n 0 f fty g gty l p
      end
    | _ ->
      begin
        let d = primary_seq n (k-1) in
        let left, left_ty = aux (k-1) in
        let innerf,innerf_ty = tgt (d'-d) f fty in
        let innerg,innerg_ty = tgt (d'-d) g gty in
        let right, right_ty = !phase (d-1) (secondary_seq n (k-1)) innerf innerf_ty innerg innerg_ty l p in
        let ld = Unchecked.dim_ty left_ty in
        let rd = Unchecked.dim_ty right_ty in
        let whisk = Functorialisation.whisk d (ld-d-1) (rd-d-1) in
        let whisk_sub_ps = Functorialisation.whisk_sub_ps (rd-d-1) left left_ty right right_ty in
        Unchecked.coh_ty whisk whisk_sub_ps
      end
  in aux (min 2 ((1 lsl (n+1))-1))
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
  let res,_ = cone_comp_n0n (d-1) (Var(f)) fty (Var(g)) gty l p in
  res

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
      let whisk_sub_ps = Functorialisation.whisk_sub_ps (d-d') ucone ucone_ty inner inner_ty in
      Unchecked.coh_ty whisk whisk_sub_ps
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
      let ctx_coned,(l',p') = cone_ctx ctx in
      let c_coned = cone_coh c l' p' in
      let _ = check_term (Ctx.check ctx_coned) c_coned in
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
  let rec aux s =
    match s with
    | [] -> []
    | (v,t)::tl ->
      let tcone = cone_tm t l2 p2 in
      (List.assoc v l1, tcone)::(aux tl)
  in List.append (aux s) ((p1,Var(p2))::s)

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
