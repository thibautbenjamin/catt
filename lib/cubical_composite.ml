open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

module F = Functorialisation

(* module Memo = struct *)
(*   let tbl_ccomp = Hashtbl.create 24 *)

(*   let find_ccomp i f = *)
(*     try Hashtbl.find tbl_ccomp i with *)
(*     | Not_found -> *)
(*       let res = f i in *)
(*       Hashtbl.add tbl_ccomp i res; *)
(*       res *)
(* end *)

module LinearComp = struct
  let tdb i = Var (Db i)

  let src_i_f i active =
    if active
    then
      let idx_src = if i = 2 then 0 else i-3 in
      let comp = Builtin.comp_n 2 in
      let sub =
        [Var (Bridge (Db (i-1))), true;
         Var (Plus (Db (i-1))), false;
         tdb i, true;
         tdb (i-1), false;
         tdb idx_src, false]
      in
      Coh(comp, sub)
    else tdb i

  let tgt_i_f i active =
    if active
    then
      let idx_src = if i = 2 then 0 else i-3 in
      let comp = Builtin.comp_n 2 in
      let sub =
        [Var (Plus (Db i)), true;
         Var (Plus (Db (i-1))), false;
         Var (Bridge (Db idx_src)), true;
         Var (Plus (Db idx_src)), false;
         tdb idx_src, false]
      in
      Coh(comp, sub)
    else Var (Plus (Db i))

  let comp_biased arity pos =
    match pos with
    | _ when pos = 0 ->
      let comp = Builtin.comp_n 2 in
      let lin_incl =
        let rec sub k =
          match k with
          | 0 -> [tdb 1, false]
          | k -> (tdb (k+2), k mod 2 == 0)::(sub(k-1))
        in sub (2*arity)
      in
      let sub =
        [Coh(Builtin.comp_n arity, lin_incl), true;
         tdb (2*arity+1), false;
         tdb 2, true;
         tdb 1, false;
         tdb 0, false]
        in Coh (comp, sub)
    | _ when pos = 2 * arity + 1 ->
      let comp = Builtin.comp_n 2 in
      let lin_incl = Unchecked.identity_ps (Builtin.ps_comp arity) in
      let sub =
        [tdb (2*arity+2), true;
         tdb (2*arity+1), false;
         Coh(Builtin.comp_n arity, lin_incl), true;
         tdb (2*arity-1), false;
         tdb 0, false]
        in Coh (comp, sub)
    | _ ->
      let comp = Builtin.comp_n arity in
      let rec sub k =
        match k with
        | _ when k = 0 -> [tdb 0, false]
        | _ when k < pos -> (tdb k, true)::(tdb (k-1), false)::(sub (k-2))
        | _ when k = pos+1 ->
          let bc = Builtin.comp_n 2 in
          let
            bcs =
            [tdb (k+2), true;
             tdb (k+1), false;
             tdb k, true;
             tdb (k-1), false;
             tdb (if k = 2 then 0 else k-3), false]
          in
          let bincomp = Coh(bc, bcs) in
          (bincomp, true)::(tdb (k+1), false)::sub(k-2)
        | _ when k > pos+1 ->
          (tdb (k+2), true)::(tdb (k+1), false)::(sub (k-2))
        |_ -> assert false
      in
      Coh (comp, sub (2*arity))

  let plus i l =
    if List.mem (Var.Db i) l then Var (Plus (Db i)) else tdb i

  let sub_whisk_i i arity l src tgt =
    let rec until k =
      match k with
      | k when k = 0 -> [tdb 0, false]
      | k when k < i -> (tdb k, true)::(tdb (k-1), false)::(until (k-2))
      | k when k = i ->
        List.append
          [Var (Bridge (Db i)), true; tgt, false; src, false; Var (Plus (Db (i-1))), false]
          (until (i-2))
      | k when k > i -> (plus k l, true)::(plus (k-1) l, false)::(until (k-2))
      | _ -> assert false
    in until (2*arity)

  let sub_assc_i i arity l =
    let rec until k =
      match k with
      | k when k = 0 && i = 0 -> [Var (Bridge (Db 0)), true ;Var (Plus (Db 0)), false ;tdb 0, false]
      | k when k = 0 -> [tdb 0, false]
      | k when k < i+1 -> (tdb k, true)::(tdb (k-1), false)::(until (k-2))
      | k when k = i+1 ->
        List.append
          [Var (Bridge (Db i)), true; Var (Plus (Db i)), false ;tdb k, true; tdb i, false]
          (until (k-2))
      | k when k > i+1 -> (plus k l, true)::(plus (k-1) l, false)::(until (k-2))
      | _ -> assert false
    in until (2*arity)

  let assc i arity l =
    let src = comp_biased arity (if i = 0 then 1 else i+2) in
    let tgt = comp_biased arity i in
    let assc = Coh.check_inv (Builtin.ps_comp (arity+1)) src tgt ("builtin_assc",0,[])in
    let sub = sub_assc_i i arity l in
    let _,ty,_ = Coh.forget assc in
    Coh (assc, sub), Unchecked.ty_apply_sub_ps ty sub

  let fun_at_i i arity l =
    let src = src_i_f i (List.mem (Var.Db i) l) in
    let tgt = tgt_i_f i (List.mem (Var.Db i) l) in
    let sub = sub_whisk_i i arity l src tgt in
    let comp = Builtin.comp_n arity in
    let whsk  = F.coh_depth0 comp [Db i] in
    let _,ty,_ = Coh.forget whsk in
    Coh(whsk, sub), Unchecked.ty_apply_sub_ps ty sub

  let move_at v l arity =
    let mv,ty =
      match v with
      | Var.Db i when i  = 0 -> assc 0 arity l
      | Var.Db i when i mod 2 = 0 -> fun_at_i i arity l
      | Var.Db i -> assc i arity l
      | _ -> Error.fatal "cubical composite can only compute on De Bruijn variables"
    in
    match ty with
    | Arr(_,s,t) -> mv,s,t
    | _ -> assert false

  let cubical arity list =
    let rec sub ctx ?(add_src=false) onto =
      match ctx with
      | [] -> onto
      | [v,_] ->
        if List.mem v list then
          let mv,_,tgtv = move_at v list arity in
          (mv,true)::(tgtv, false)::onto
        else onto
      | (v,_)::(tv,_)::ctx ->
        let onto =
          if List.mem v list then
            let mv,src,tgt = move_at v list arity in
            if List.mem tv list then
              let mtv,srctv,tgttv = move_at tv list arity in
              (mv,true)::(tgt, false)::(mtv,true)::(tgttv, false)::(if add_src then (srctv,false)::onto else onto)
            else (mv,true)::(tgt, false)::(if add_src then (src,false)::onto else onto)
          else onto
        in sub ctx onto
    in
    if arity = 1 then Var (Bridge (Db 2)) else
      let comp = Suspension.coh (Some 1) (Builtin.comp_n (List.length list)) in
      let s = sub (Unchecked.ps_to_ctx (Builtin.ps_comp arity)) ~add_src:true [plus (2*arity-1) list, false; tdb 0, false] in
      Coh (comp, s)
end

let tdb i = Var (Db i)
let comp_n_l n = if n = 0 then tdb 0 else tdb ((2*n)-1)
let comp_n_r n = tdb ((2*n)+1)
let comp_n_m n = tdb ((2*n)+2)
let rec comp_kn_sub_ps k n = if n = 0 then [(comp_n_m k,true);(comp_n_r k,false);(comp_n_l k,false)] else (comp_n_m (k+n),true)::(comp_n_r (k+n),false)::(comp_kn_sub_ps k (n-1))
let comp_kn_tm k n = Coh(Builtin.comp_n n, comp_kn_sub_ps k (n-1))
let comp_n_tm n = comp_kn_tm 0 n


let sqtl_db n = if n = 0 then 0 else ((n*6)-3)
let sqtl n = tdb (sqtl_db n)
let sqbl n = tdb ((sqtl_db n)+1)
let sqml n = tdb ((sqtl_db n)+2)
let sqtr n = tdb (sqtl_db (n+1))
let sqbr n = tdb ((sqtl_db (n+1))+1)
let sqmr n = tdb ((sqtl_db (n+1))+2)
let sqtm n = tdb ((sqtl_db (n+1))+3)
let sqbm n = tdb ((sqtl_db (n+1))+4)

(* let rec build_ccomp_n arity = *)
(* and ccomp_n arity = *)
(*   Memo.find_ccomp arity build_ccomp_n *)

let src_ccomp arity =
  let line = if arity = 1 then
      sqtm 0
    else
      let comp = Builtin.comp_n arity in
      let rec sub i =
        if i <= 0 then [sqtl 0, false]
        else (sqtm (i-1), true)::(sqtl i, false)::(sub (i-1))
      in
      Coh(comp, (sub arity))
  in
  Coh(Builtin.comp_n 2, [sqmr (arity - 1), true; sqbr (arity - 1), false; line, true; sqtr (arity - 1), false; sqtl 0, false])

let tgt_ccomp arity =
  let line = if arity = 1 then
      sqbm 0
    else
      let comp = Builtin.comp_n arity in
      let rec sub i =
        if i <= 0 then [sqbl 0, false]
        else (sqbm (i-1), true)::(sqbl i, false)::(sub (i-1))
      in  Coh(comp, (sub arity))
  in
  Coh(Builtin.comp_n 2, [line, true; sqbr (arity - 1), false; sqml 0, true; sqbl 0, false; sqtl 0, false])

(* source and source inclusion of a functorialised ps *)
let ctx_src ps l =
  let d = Unchecked.dim_ps ps in
  let bdry = Unchecked.ps_bdry ps in
  let tgt_incl_ps = Unchecked.ps_tgt ps in
  let tgt_f, bdry_f, names, l = F.sub_w_tgt bdry tgt_incl_ps l in
  let src_ctx,i1,i2 = Unchecked.ps_compose (d-1) ps bdry_f in
  let in_minus = Unchecked.identity_ps ps in
  let src_incl = Unchecked.pullback_up (d-1) ps bdry_f in_minus tgt_f in
  src_ctx, src_incl, i1, i2, bdry_f, l, names

(* target and target inclusion of a functorialised ps *)
let ctx_tgt ps l =
  let d = Unchecked.dim_ps ps in
  let bdry = Unchecked.ps_bdry ps in
  let src_incl_ps = Unchecked.ps_src ps in
  let src_f, bdry_f, names, l_bdry = F.sub_w_tgt bdry src_incl_ps l in
  let tgt_ctx,i1,i2 = Unchecked.ps_compose (d-1) bdry_f ps in
  let in_plus = Unchecked.sub_to_sub_ps ps (F.tgt_subst l) in
  let tgt_incl = Unchecked.pullback_up (d-1) bdry_f ps src_f in_plus in
  tgt_ctx, tgt_incl, i1, i2, bdry_f, l_bdry, names

(* Construct source (t[i1]) * (tgt_f[i2]) *)
let naturality_src coh ty tgt ty_base dim l i1 i2 names =
  let t = Coh(coh, i1) in
  let tgt_f_ty = Unchecked.rename_ty (F.ty ty_base l tgt) names in
  let tgt_f_ty = Unchecked.ty_apply_sub_ps tgt_f_ty i2 in
  let tgt_f = Unchecked.rename_tm (F.tm_one_step_tm tgt l) names in
  let tgt_f = Unchecked.tm_apply_sub_ps tgt_f i2 in
  let coh_src_sub_ps = F.whisk_sub_ps 0 t (Unchecked.ty_apply_sub_ps ty i1) tgt_f tgt_f_ty in
  Coh(F.whisk (dim-1) 0 0,coh_src_sub_ps)

(* Construct target (src_f[i1]) * (t[i2]) *)
let naturality_tgt coh ty src ty_base dim l i1 i2 names =
  let t = Coh(coh, i2) in
  let src_f_ty = Unchecked.rename_ty (F.ty ty_base l src) names in
  let src_f_ty = Unchecked.ty_apply_sub_ps src_f_ty i1 in
  let src_f = Unchecked.rename_tm (F.tm_one_step_tm src l) names in
  let src_f = Unchecked.tm_apply_sub_ps src_f i1 in
  let coh_tgt_sub_ps = F.whisk_sub_ps 0 src_f src_f_ty t (Unchecked.ty_apply_sub_ps ty i2) in
  Coh(F.whisk (dim-1) 0 0,coh_tgt_sub_ps)

let biasor_sub_intch_src ps bdry_f i1 i2 d =
  let ps_red = Ps_reduction.reduce (d-1) ps in
  let prod,_,_ = Unchecked.ps_compose (d-1) ps_red bdry_f in
  let red_sub_prod = Ps_reduction.reduction_sub prod in
  let red_sub_ps = Ps_reduction.reduction_sub ps in
  let left_leg = Unchecked.sub_ps_apply_sub_ps red_sub_ps i1 in
  let prod_to_src = Unchecked.pullback_up (d-1) ps_red bdry_f left_leg i2 in
  Unchecked.sub_ps_apply_sub_ps red_sub_prod prod_to_src

let biasor_sub_intch_tgt ps bdry_f i1 i2 d =
  let ps_red = Ps_reduction.reduce (d-1) ps in
  let prod,_,_ = Unchecked.ps_compose (d-1) bdry_f ps_red in
  let red_sub_prod = Ps_reduction.reduction_sub prod in
  let red_sub_ps = Ps_reduction.reduction_sub ps in
  let right_leg = Unchecked.sub_ps_apply_sub_ps red_sub_ps i2 in
  let prod_to_src = Unchecked.pullback_up (d-1) bdry_f ps_red i1 right_leg in
  Unchecked.sub_ps_apply_sub_ps red_sub_prod prod_to_src

(* Interchange needed for source of depth-1 non-inv coh *)
(*
https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXHBhcnRpYWxcXEdhbW1hIl0sWzIsMSwiXFxvdmVycmlnaHRhcnJvd3tcXHBhcnRpYWxcXEdhbW1hfV57WF9cXHRhdX0iXSxbMCwzLCJcXEdhbW1hIl0sWzAsMSwiXFxHYW1tYV57cmVkfSJdLFsxLDIsIlxcRGVsdGEiXSxbMSwzLCJcXFBoaSJdLFszLDIsIlxcRGVsdGFee3JlZH0iXSxbMSw0LCJcXG92ZXJyaWdodGFycm93e1xcR2FtbWF9XlgiXSxbMCwxLCJcXHNpZ21hIl0sWzAsMiwiXFx0YXUiLDEseyJsYWJlbF9wb3NpdGlvbiI6NzAsImN1cnZlIjo1fV0sWzMsMiwiXFxyaG9fXFxHYW1tYSIsMl0sWzAsMywiXFx0YXVfciIsMV0sWzEsNCwial8yIiwxXSxbMyw0LCJqXzEiLDFdLFs0LDAsIiIsMCx7InN0eWxlIjp7Im5hbWUiOiJjb3JuZXIifX1dLFs0LDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDUsImlfMSIsMV0sWzEsNSwiaV8yIiwxXSxbNSwwLCIiLDEseyJzdHlsZSI6eyJuYW1lIjoiY29ybmVyIn19XSxbNiw0LCJcXHJob19cXERlbHRhIiwxLHsiY3VydmUiOjF9XSxbMiw3XSxbMSw3LCJcXG92ZXJyaWdodGFycm93e1xcdGF1fV5YIiwxLHsiY3VydmUiOi0zfV0sWzUsNywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
 *)
let depth1_interchanger_src coh coh_bridge l =
  let gamma,coh_ty,_ = Coh.forget coh in
  let _,tgt,ty_base = Coh.noninv_srctgt coh in
  let d = Unchecked.dim_ps gamma in
  let src_ctx, src_incl, i1, i2, bdry_f, l_tgt, names = ctx_src gamma l in
  let coh_src = naturality_src coh coh_ty tgt ty_base d l_tgt i1 i2 names in
  let coh_tgt = Coh(coh_bridge, biasor_sub_intch_src gamma bdry_f i1 i2 d) in
  (* Construct final coherence *)
  let intch_coh = Coh.check_inv src_ctx coh_src coh_tgt ("intch_src",0,[]) in
  let _,ty,_ = Coh.forget intch_coh in
  let intch = Coh(intch_coh,src_incl) in
  let ty = Unchecked.ty_apply_sub_ps ty src_incl in
  intch, ty

let depth1_interchanger_tgt coh coh_bridge l =
  let gamma,coh_ty,_ = Coh.forget coh in
  let src,_,ty_base = Coh.noninv_srctgt coh in
  let d = Unchecked.dim_ps gamma in
  let tgt_ctx,tgt_incl, i1, i2, bdry_f, l_src, names = ctx_tgt gamma l in
  let coh_tgt = naturality_tgt coh coh_ty src ty_base d l_src i1 i2 names in
  let coh_src = Coh(coh_bridge, biasor_sub_intch_tgt gamma bdry_f i1 i2 d) in
  let intch_coh = Coh.check_inv tgt_ctx coh_src coh_tgt ("intch_tgt",0,[]) in
  let _,ty,_ = Coh.forget intch_coh in
  let intch = Coh(intch_coh,tgt_incl) in
  let ty = Unchecked.ty_apply_sub_ps ty tgt_incl in
  intch, ty

(*
  Compare substitutions out of the same ps-context
  and fill gaps between matching but different terms with
  the correct cubical composite
 *)
let depth1_bridge_sub ps_inter l_inter d =
  let rec aux red =
    match red with
    | [] -> []
    | (t,true)::(w,false)::red ->
      let ps_comp,s =
        match t with
        | Coh(comp,s) ->
          let ps_comp,_,_ = Coh.forget comp in
          ps_comp,s
        | Var v ->
          let ty,_ = List.assoc v (Unchecked.ps_to_ctx ps_inter) in
          let s = (Var v,true)::(Unchecked.ty_to_sub_ps ty) in
          let ps_comp = Suspension.ps (Some (Unchecked.dim_ty ty)) (Br[]) in
          ps_comp,s
        | Meta_tm _ -> Error.fatal "meta_variables must have been resolved"
      in
      let l = F.preimage (Unchecked.ps_to_ctx ps_comp) s l_inter in
      if l <> [] then
        let arity = (List.length l - 1)/2 in
        let s_tmp = F.sub (Unchecked.sub_ps_to_sub s) l in
        let s = F.sub_ps s l_inter in
        let w_plus = Unchecked.tm_apply_sub w (F.tgt_subst l_inter) in
        let src = Suspension.tm (Some (d-1)) (src_ccomp arity) in
        let tgt = Suspension.tm (Some (d-1)) (tgt_ccomp arity) in
        (* --------------------------------------------------------- *)
        let cubical_comp = LinearComp.cubical arity (List.init (2*arity+1) (fun i -> Var.Db i)) in
        let ccomp_tmp = Suspension.tm (Some (d-1)) (cubical_comp) in
        let ccomp_tmp = Unchecked.tm_apply_sub ccomp_tmp s_tmp in
        (ccomp_tmp, true)::
        (Unchecked.tm_apply_sub_ps tgt s, false)::
        (Unchecked.tm_apply_sub_ps src s, false)::
        (w_plus,false)::(aux red)
        (* --------------------------------------------------------- *)
      else
        (t,true)::(w,false)::(aux red)
    | (t,e)::red -> (t,e)::(aux red)
  in aux (Ps_reduction.reduction_sub ps_inter)

let loc_max_dim d ps x =
  let ctx = Unchecked.ps_to_ctx ps in
  let ty,expl = List.assoc x ctx in
  expl &&  (Unchecked.dim_ty ty = d)

let intermediate_ps ps l d =
  let l_d0,l_d1 = List.partition (loc_max_dim (d-1) ps) l in
  if l_d0 = [] then
    ps,l,Unchecked.(sub_ps_to_sub (identity_ps ps))
  else
  let ps_f_c = F.ctx (Unchecked.ps_to_ctx ps) l_d0 in
  let _,names,_ = Unchecked.db_levels ps_f_c in
  let ps_f = PS.(forget (mk (Ctx.check ps_f_c))) in
  let l_psf = (List.map (fun x -> Var.Db (List.assoc x names)) l_d1) in
  let names = List.map (fun (x,n) -> (Var.Db n, Var x)) names in
  ps_f, l_psf, names

let bridge_ps ps_inter l_inter d =
  let red_sub = Ps_reduction.reduction_sub ps_inter in
  let ps_red = Ps_reduction.reduce (d-1) ps_inter in
  let ps_red_c = Unchecked.ps_to_ctx ps_red in
  let coh_l = F.preimage ps_red_c red_sub l_inter in
  let coh_l = List.filter (loc_max_dim d ps_red) coh_l in
  ps_red, coh_l

let bridge_coh coh ps_bridge =
  let _,_,name = Coh.forget coh in
  let src,tgt,_ = Coh.noninv_srctgt coh in
  let name_red = Unchecked.full_name name^"_red",0,[] in
  let coh_bridge = Coh.check_noninv ps_bridge src tgt name_red in
  coh_bridge

let coh_depth1 coh l =
  let ps,_,_ = Coh.forget coh in
  let d = Unchecked.dim_ps ps in
  let ps_inter, l_inter, names = intermediate_ps ps l d in
  let ps_bridge, l_bridge = bridge_ps ps_inter l_inter d in
  let coh_bridge = bridge_coh coh ps_bridge in
  let intch_src,intch_src_ty = depth1_interchanger_src coh coh_bridge l in
  let intch_tgt,intch_tgt_ty = depth1_interchanger_tgt coh coh_bridge l in
  let bridge = depth1_bridge_sub ps_inter l_inter d in
  let bridge = Unchecked.sub_ps_apply_sub bridge (F.sub names l_inter) in
  let coh_bridge_f = F.coh_depth0 coh_bridge l_bridge in
  let middle = Coh(coh_bridge_f, bridge) in
  let inner_tgt,final_tgt =
    match intch_tgt_ty with
    |  Arr(_,t,t') -> t,t'
    | _ -> assert false
  in
  let comp_sub_ps =
    List.append
      [intch_tgt,true;final_tgt,false;middle,true;inner_tgt,false;intch_src,true]
      (Unchecked.ty_to_sub_ps intch_src_ty)
  in
  let comp = Suspension.coh (Some d) (Builtin.comp_n 3) in
  Coh(comp, comp_sub_ps), F.ctx (Unchecked.ps_to_ctx ps) l

let init () =
  F.coh_depth1 := coh_depth1
