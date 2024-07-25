open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

module F = Functorialisation

module Memo = struct
  let tbl_ccomp = Hashtbl.create 24

  let find_ccomp i f =
    try Hashtbl.find tbl_ccomp i with
    | Not_found ->
      let res = f i in
      Hashtbl.add tbl_ccomp i res;
      res
end

let tdb i = Var (Db i)
(* DB level for the source, target and middle of the n-th locally maximal variable in a linear composite *)
let comp_n_l n = if n = 0 then tdb 0 else tdb ((2*n)-1)
let comp_n_r n = tdb ((2*n)+1)
let comp_n_m n = tdb ((2*n)+2)
(* n-ary linear composite of the k-th to (n+k)-th variables *)
let rec comp_kn_sub_ps k n = if n = 0 then [(comp_n_m k,true);(comp_n_r k,false);(comp_n_l k,false)] else (comp_n_m (k+n),true)::(comp_n_r (k+n),false)::(comp_kn_sub_ps k (n-1))
let comp_kn_tm k n = Coh(Builtin.comp_n n, comp_kn_sub_ps k (n-1))
let comp_n_tm n = comp_kn_tm 0 n
(* short-hands for unary and binary composites *)
let comp_unary x y f = Coh(Builtin.comp_n 1, [(f,true);(y,false);(x,false)])
let comp_binary x y f z g = Coh(Builtin.comp_n 2, [(g,true);(z,false);(f,true);(y,false);(x,false)])
(*
  DB levels of the n-th square in the naturality of linear composite
  Refer to the diagram below:
  https://q.uiver.app/#q=WzAsOSxbMCwxLCJcXHRleHR7c3F0bCAwfSJdLFsyLDEsIlxcdGV4dHtzcXRsIDF9Il0sWzIsMywiXFx0ZXh0e3NxYmwgMX0iXSxbMCwzLCJcXHRleHR7c3FibCAwfSJdLFs0LDEsIlxcdGV4dHtzcXRyIDF9Il0sWzQsMywiXFx0ZXh0e3NxYnIgMX0iXSxbMCwwLCJcXHRleHR7Y29tcFxcX25cXF9sIDB9Il0sWzIsMCwiXFx0ZXh0e2NvbXBcXF9uXFxfciAwfSJdLFs0LDAsIlxcdGV4dHtjb21wXFxfblxcX3IgMX0iXSxbMCwxLCJcXHRleHR7c3F0bSAwfSIsMV0sWzEsMiwiXFx0ZXh0e3NxbWwgMX0iLDFdLFswLDMsIlxcdGV4dHtzcW1sIDB9IiwxXSxbMywyLCJcXHRleHR7c3FibSAwfSIsMV0sWzEsNCwiXFx0ZXh0e3NxdG0gMX0iLDFdLFs0LDUsIlxcdGV4dHtzcW1yIDF9IiwxXSxbMiw1LCJcXHRleHR7c3FibSAxfSIsMV0sWzYsNywiXFx0ZXh0e2NvbXBcXF9uXFxfbSAwfSJdLFs3LDgsIlxcdGV4dHtjb21wXFxfblxcX20gMX0iXSxbMywxLCJcXHRleHR7c3FtbSAwfSIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sImxldmVsIjoyfV0sWzIsNCwiXFx0ZXh0e3NxbW0gMX0iLDEseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9LCJsZXZlbCI6Mn1dXQ==
*)
let sqtl_db n = if n = 0 then 0 else ((n*6)-3)
let sqtl n = tdb (sqtl_db n)
let sqbl n = tdb ((sqtl_db n)+1)
let sqml n = tdb ((sqtl_db n)+2)
let sqtr n = tdb (sqtl_db (n+1))
let sqbr n = tdb ((sqtl_db (n+1))+1)
let sqmr n = tdb ((sqtl_db (n+1))+2)
let sqtm n = tdb ((sqtl_db (n+1))+3)
let sqbm n = tdb ((sqtl_db (n+1))+4)
let sqmm n = tdb ((sqtl_db (n+1))+5)
(* The source and target of the square *)
let sqb_sub_ps n = [(sqbm n,true);(sqbr n,false);(sqml n,true);(sqbl n,false);(sqtl n,false)]
let sqt_sub_ps n = [(sqmr n,true);(sqbr n,false);(sqtm n,true);(sqtr n,false);(sqtl n,false)]
let sqb n = Coh(Builtin.comp_n 2, sqb_sub_ps n)
let sqt n = Coh(Builtin.comp_n 2, sqt_sub_ps n)
(* The composite of bottoms and tops of n successive squares *)
let rec sqb_comp_sub_ps n = if n = 0 then [(sqbm 0,true);(sqbr 0,false);(sqbl 0,false)] else (sqbm n,true)::(sqbr n,false)::(sqb_comp_sub_ps (n-1))
let rec sqt_comp_sub_ps n = if n = 0 then [(sqtm 0,true);(sqtr 0,false);(sqtl 0,false)] else (sqtm n,true)::(sqtr n,false)::(sqt_comp_sub_ps (n-1))
let sqb_comp n = Coh(Builtin.comp_n n, sqb_comp_sub_ps (n-1))
let sqt_comp n = Coh(Builtin.comp_n n, sqt_comp_sub_ps (n-1))
(* The source and target of n successive squares composed *)
let rec sqb_corner_comp_sub_ps n = if n = 0 then (sqb_sub_ps 0) else (sqbm n,true)::(sqbr n,false)::(sqb_corner_comp_sub_ps (n-1))
let sqt_corner_comp_sub_ps n = (sqmr n,true)::(sqbr n,false)::(sqt_comp_sub_ps n)

(*
https://q.uiver.app/#q=WzAsNCxbMCwwLCIwIl0sWzIsMCwiMyJdLFsyLDIsIjQiXSxbMCwyLCIxIl0sWzEsMiwiNSIsMV0sWzAsMywiMiIsMV0sWzEsMywiOCIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sImxldmVsIjoyfV0sWzAsMSwiNiIsMV0sWzMsMiwiNyIsMV0sWzMsMiwiNyIsMSx7ImN1cnZlIjozfV0sWzAsMSwiNiIsMSx7ImN1cnZlIjotM31dLFs4LDksIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbMTAsNywiIiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==
*)
let ccomp_unary =
    let unbias = comp_n_tm 2 in
    let biasl = comp_binary (tdb 0) (tdb 1) (comp_unary (tdb 0) (tdb 1) (tdb 2)) (tdb 3) (tdb 4) in
    let biasr = comp_binary (tdb 0) (tdb 1) (tdb 2) (tdb 3) (comp_unary (tdb 1) (tdb 3) (tdb 4)) in
    (* Phase 1 *)
    let phase1_sub_ps = sqt_sub_ps 0 in
    let phase1 = Coh(Coh.check_inv (Builtin.ps_comp 2) biasl unbias ("builtin_unbiasl",0,[]),phase1_sub_ps) in
    let phase1_sub_contr = Unchecked.coh_to_sub_ps phase1 in
    (* Phase 2 *)
    let phase2_sub_contr = [(sqmm 0,true);(sqb 0,false)] in
    (* Phase 3 *)
    let phase3_sub_ps = sqb_sub_ps 0 in
    let phase3_sub = Unchecked.sub_ps_to_sub phase3_sub_ps in
    let phase3 = Coh(Coh.check_inv (Builtin.ps_comp 2) unbias biasr ("builtin_biasr",0,[]),phase3_sub_ps) in
    let phase3_sub_contr = [(phase3,true);(Unchecked.tm_apply_sub biasr phase3_sub,false)] in
    (* Collate *)
    let comp_sub = List.concat [phase3_sub_contr;phase2_sub_contr;phase1_sub_contr] in
    let comp = Suspension.coh (Some(1)) (Builtin.comp_n 3) in
    Coh(comp,comp_sub)

(*
https://q.uiver.app/#q=WzAsOSxbMCwxLCIwIl0sWzIsMSwiMyJdLFsyLDMsIjQiXSxbMCwzLCIxIl0sWzQsMSwiOSJdLFs0LDMsIjEwIl0sWzAsMCwiMCJdLFsyLDAsIjEiXSxbNCwwLCIzIl0sWzAsMSwiNiIsMV0sWzEsMiwiNSIsMV0sWzAsMywiMiIsMV0sWzMsMiwiNyIsMV0sWzEsNCwiMTIiLDFdLFs0LDUsIjExIiwxXSxbMiw1LCIxMyIsMV0sWzYsNywiMiIsMV0sWzcsOCwiNCIsMV0sWzMsMSwiOCIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sImxldmVsIjoyfV0sWzIsNCwiMTQiLDEseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9LCJsZXZlbCI6Mn1dXQ==
*)

let ccomp_binary =
    let assocr = comp_binary (tdb 0) (tdb 1) (tdb 2) (tdb 5) (comp_binary (tdb 1) (tdb 3) (tdb 4) (tdb 5) (tdb 6)) in
    let assocl = comp_binary (tdb 0) (tdb 3) (comp_n_tm 2) (tdb 5) (tdb 6) in
    (* Phase 1 *)
    let phase1_sub_ps = sqt_corner_comp_sub_ps 1 in
    let phase1 = Coh(Coh.check_inv (Builtin.ps_comp 3) assocl assocr ("builtin_assoc",0,[]),phase1_sub_ps) in
    let phase1_sub_contr = Unchecked.coh_to_sub_ps phase1 in
    (* Phase 2 *)
    let phase2_sub_ps = [(sqmm 1,true);(sqb 1,false);(sqt 1,false);(sqbr 1,false);(sqtm 0,true);(sqtr 0,false);(sqtl 0,false)] in
    let phase2 = Coh(F.whisk 0 0 1, phase2_sub_ps) in
    let phase2_sub_contr = [(phase2,true);(comp_binary (sqtl 0) (sqtr 0) (sqtm 0) (sqbr 1) (sqb 1),false)] in
    (* Phase 3 *)
    let phase3_sub_ps = List.concat [[(sqbm 1,true);(sqbr 1,false)];(sqt_sub_ps 0)] in
    let phase3_sub = Unchecked.list_to_db_level_sub (List.map fst phase3_sub_ps) in
    let phase3 = Coh(Coh.check_inv (Builtin.ps_comp 3) assocr assocl ("builtin_assoc_inv",0,[]),phase3_sub_ps) in
    let phase3_sub_contr = [(phase3,true);(Unchecked.tm_apply_sub assocl phase3_sub,false)] in
    (* Phase 4 *)
    let phase4_sub_ps = [(sqbm 1,true);(sqbr 1,false);(sqmm 0,true);(sqb 0,false);(sqt 0,false);(sqbr 0,false);(sqtl 0,false)] in
    let phase4 = Coh(F.whisk 0 1 0,phase4_sub_ps) in
    let phase4_sub_contr = [(phase4,true);(comp_binary (sqtl 0) (sqbr 0) (sqb 0) (sqbr 1) (sqbm 1),false)] in
    (* Phase 5 *)
    let phase5_sub_ps = List.concat [[(sqbm 1,true);(sqbr 1,false)];(sqb_sub_ps 0)] in
    let phase5_sub = Unchecked.list_to_db_level_sub (List.map fst phase5_sub_ps) in
    let phase5 = Coh(Coh.check_inv (Builtin.ps_comp 3) assocl assocr ("builtin_assoc",0,[]),phase5_sub_ps) in
    let phase5_sub_contr = [(phase5,true);(Unchecked.tm_apply_sub assocr phase5_sub,false)] in
    (* Collate *)
    let comp_sub = List.concat [phase5_sub_contr;phase4_sub_contr;phase3_sub_contr;phase2_sub_contr;phase1_sub_contr] in
    let comp = Suspension.coh (Some(1)) (Builtin.comp_n 5) in
    Coh(comp,comp_sub)

let rec build_ccomp_n arity =
    match arity with
    | 1 -> ccomp_unary
    | 2 -> ccomp_binary
    | _ -> begin
      (* Compute inductive case *)
      let sq_ind = ccomp_n (arity-1) in
      (* Compute various biased composites *)
      let ps = Builtin.ps_comp (arity+1) in
      let unbiasl = comp_binary (comp_n_l 0) (comp_n_r (arity-1)) (comp_n_tm arity) (comp_n_r arity) (comp_n_m arity) in
      let unbiasr = comp_binary (comp_n_l 0) (comp_n_r 0) (comp_n_m 0) (comp_n_r arity) (comp_kn_tm 1 arity) in
      let biasl = comp_binary (comp_n_l 0) (comp_n_r (arity-1)) (comp_binary (comp_n_l 0) (comp_n_r (arity-2)) (comp_n_tm (arity-1)) (comp_n_r (arity-1)) (comp_n_m (arity-1))) (comp_n_r arity) (comp_n_m arity) in
      let biasr = comp_binary (comp_n_l 0) (comp_n_r 0) (comp_n_m 0) (comp_n_r arity) (comp_binary (comp_n_l 1) (comp_n_r (arity-1)) (comp_kn_tm 1 (arity-1)) (comp_n_r arity) (comp_n_m arity)) in
      let sqb_corner_sub_ps = sqb_corner_comp_sub_ps (arity-1) in
      let sqb_corner_sub = Unchecked.sub_ps_to_sub sqb_corner_sub_ps in
      (* Phase 1 *)
      let phase1 = Coh(Coh.check_inv ps unbiasl biasl ("builtin_bias_left",0,[]), sqt_corner_comp_sub_ps (arity-1)) in
      (* Phase 2 *)
      let phase2_presub = [sqmm (arity-1);sqbm (arity-1);sqtm (arity-1);sqmr (arity-1);sqbr (arity-1);sqtr (arity-1);sq_ind;sqb_comp (arity-1);sqt_comp (arity-1);sqml (arity-1);sqbl (arity-1);sqtl (arity-1);sqml 0;sqbl 0;sqtl 0] in
      let phase2_sub = Unchecked.list_to_db_level_sub phase2_presub in
      let phase2 = Unchecked.tm_apply_sub ccomp_binary phase2_sub in
      let phase2_tgt = Unchecked.tm_apply_sub biasr sqb_corner_sub in
      (* Phase 3 *)
      let phase3 = Coh(Coh.check_inv ps biasr unbiasr ("builtin_bias_right",0,[]), sqb_corner_sub_ps) in
      let phase3_tgt = Unchecked.tm_apply_sub unbiasr sqb_corner_sub in
      (* Merge *)
      let comp_sub = List.concat [[(phase3,true);(phase3_tgt,false);(phase2,true);(phase2_tgt,false)];(Unchecked.coh_to_sub_ps phase1)] in
      Coh(Suspension.coh (Some(1)) (Builtin.comp_n 3), comp_sub)
    end
and ccomp_n arity =
  Memo.find_ccomp arity build_ccomp_n

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
  let _,intch_ty,_ = Coh.forget intch_coh in
  let intch = Coh(intch_coh,src_incl) in
  intch, Unchecked.ty_apply_sub_ps intch_ty src_incl

let depth1_interchanger_tgt coh coh_bridge l =
  let gamma,coh_ty,_ = Coh.forget coh in
  let src,_,ty_base = Coh.noninv_srctgt coh in
  let d = Unchecked.dim_ps gamma in
  let tgt_ctx,tgt_incl, i1, i2, bdry_f, l_src, names = ctx_tgt gamma l in
  let coh_tgt = naturality_tgt coh coh_ty src ty_base d l_src i1 i2 names in
  let coh_src = Coh(coh_bridge, biasor_sub_intch_tgt gamma bdry_f i1 i2 d) in
  let intch_coh = Coh.check_inv tgt_ctx coh_src coh_tgt ("intch_tgt",0,[]) in
  let _,intch_ty,_ = Coh.forget intch_coh in
  let intch = Coh(intch_coh,tgt_incl) in
  intch, Unchecked.ty_apply_sub_ps intch_ty tgt_incl

(*
  Compare substitutions out of the same ps-context
  and fill gaps between matching but different terms with
  the correct cubical composite
 *)
let rec depth1_bridge_sub src_sub tgt_sub l =
  match src_sub,tgt_sub with
  | [],[] -> []
  | (src,expl)::src_tl,(tgt,_)::tgt_l ->
    begin
      let rest = depth1_bridge_sub src_tl tgt_l l in
      try
        let _ = Unchecked.check_equal_tm src tgt in
        (src,expl)::rest
      with NotEqual(_) ->
        let (_,ty,_),src_sub = match src with
          | Coh(c,s) -> Coh.forget c,s
          | _ -> assert false in
        let d = Unchecked.dim_ty ty in
        let src_bridge = fst (List.nth src_sub 2) in
        let inner_sub,arity = match src_bridge with
          | Coh(_,s) -> s,((List.length s)-(2*d))/2+1
          | _ -> assert false in
        let ccomp = Suspension.tm (Some(d-1)) (ccomp_n arity) in
        let inner_subf = F.sub inner_sub l in
        let inner_subf_norm = Unchecked.list_to_db_level_sub (List.map fst inner_subf) in
        let bridge = Unchecked.tm_apply_sub ccomp inner_subf_norm in
        (bridge,expl)::(tgt,false)::(src,false)::rest
    end
  | _,_ -> assert false

let image ctx sub l =
  let idx_image v =
    match List.assoc v sub with
    | Coh _ | Meta_tm _ -> Error.fatal "image can only be taken with variables"
    | Var v -> v
  in
  let rec discard_non_closed l =
    match l with
    | [] -> []
    | v::l ->
      let
        closure =
        List.filter
          (fun (_,(ty,_)) -> Unchecked.ty_contains_var ty v)
          ctx
      in
      if List.for_all (fun (x,_) -> List.mem x l) closure
      then v::(discard_non_closed l)
      else (discard_non_closed l)
  in
  let img = List.map idx_image l in
  discard_non_closed img

(* Pasting scheme (Γ_red * ∂Γ_f)red = (∂Γ_f * Γ_red)red = (Γ * ∂Γ_f)_red *)
let bridge_ps ps l =
  let d = Unchecked.dim_ps ps in
  let bdry = Unchecked.ps_bdry ps in
  let src = Unchecked.ps_src ps in
  let src_preim = F.preimage (Unchecked.ps_to_ctx bdry) src l in
  let bdry_f,_ = F.ps bdry src_preim in
  let ps,_,i2 = Unchecked.ps_compose (d-1) bdry_f ps in
  let i2 = Unchecked.sub_ps_to_sub i2 in
  let ps_c = Unchecked.ps_to_ctx ps in
  let red_sub = Ps_reduction.reduction_sub ps in
  let ps_red = Ps_reduction.reduce (d-1) ps in
  let ps_red_c = Unchecked.ps_to_ctx ps_red in
  let coh_l = F.preimage ps_red_c red_sub (image ps_c i2 l) in
  ps_red, coh_l

let bridge_coh coh l =
  let ps,_,name = Coh.forget coh in
  let src,tgt,_ = Coh.noninv_srctgt coh in
  let ps_bridge, coh_l = bridge_ps ps l in
  let name_red = Unchecked.full_name name^"_red",0,[] in
  let coh_bridge = Coh.check_noninv ps_bridge src tgt name_red in
  let coh_bridge_f = F.coh_depth0 coh_bridge coh_l in
  coh_bridge, coh_bridge_f

let coh_depth1 coh l =
  let ps,_,_ = Coh.forget coh in
  let coh_bridge, coh_bridge_f = bridge_coh coh l in
  let intch_src,intch_src_ty = depth1_interchanger_src coh coh_bridge l in
  let intch_tgt,intch_tgt_ty = depth1_interchanger_tgt coh coh_bridge l in
  let base_ty,inner_src,inner_tgt,final_tgt =
    match intch_src_ty,intch_tgt_ty with
    | Arr(b,_,s), Arr(_,t,t') -> b,s,t,t'
    | _,_ -> assert false
  in
  let src_sub_ps,tgt_sub_ps =
    match inner_src,inner_tgt with
    | Coh(_,s), Coh(_,s') -> s,s'
    | _,_ -> assert false in
  let bridge = depth1_bridge_sub src_sub_ps tgt_sub_ps l in
  let middle = Coh(coh_bridge_f, bridge) in
  (* Combine *)
  let comp_sub_ps =
    List.append
      [intch_tgt,true;final_tgt,false;middle,true;inner_tgt,false;intch_src,true]
      (Unchecked.ty_to_sub_ps intch_src_ty)
  in
  let d = Unchecked.dim_ty base_ty in
  let comp = Suspension.coh (Some d) (Builtin.comp_n 3) in
  Coh(comp, comp_sub_ps), F.ctx (Unchecked.ps_to_ctx ps) l

let init () =
  F.coh_depth1 := coh_depth1
