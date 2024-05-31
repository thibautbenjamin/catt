open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

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
let comp_n_l n = if n = 0 then tdb 0 else tdb ((2*n)-1)
let comp_n_r n = tdb ((2*n)+1)
let comp_n_m n = tdb ((2*n)+2)
let rec comp_kn_sub_ps k n = if n = 0 then [(comp_n_m k,true);(comp_n_r k,false);(comp_n_l k,false)] else (comp_n_m (k+n),true)::(comp_n_r (k+n),false)::(comp_kn_sub_ps k (n-1))
let comp_kn_tm k n = Coh(Builtin.comp_n n, comp_kn_sub_ps k (n-1))
let comp_n_tm n = comp_kn_tm 0 n
let comp_unary x y f = Coh(Builtin.comp_n 1, [(f,true);(y,false);(x,false)])
let comp_binary x y f z g = Coh(Builtin.comp_n 2, [(g,true);(z,false);(f,true);(y,false);(x,false)])
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
let sqb_sub_ps n = [(sqbm n,true);(sqbr n,false);(sqml n,true);(sqbl n,false);(sqtl n,false)]
let sqt_sub_ps n = [(sqmr n,true);(sqbr n,false);(sqtm n,true);(sqtr n,false);(sqtl n,false)]
let sqb n = Coh(Builtin.comp_n 2, sqb_sub_ps n)
let sqt n = Coh(Builtin.comp_n 2, sqt_sub_ps n)
let rec sqb_comp_sub_ps n = if n = 0 then [(sqbm 0,true);(sqbr 0,false);(sqbl 0,false)] else (sqbm n,true)::(sqbr n,false)::(sqb_comp_sub_ps (n-1))
let rec sqt_comp_sub_ps n = if n = 0 then [(sqtm 0,true);(sqtr 0,false);(sqtl 0,false)] else (sqtm n,true)::(sqtr n,false)::(sqt_comp_sub_ps (n-1))
let sqb_comp n = Coh(Builtin.comp_n n, sqb_comp_sub_ps (n-1))
let sqt_comp n = Coh(Builtin.comp_n n, sqt_comp_sub_ps (n-1))
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
    let phase1 = Coh(Coh.check_inv (Builtin.ps_comp 2) biasl unbias ("builtin_unbiasl",0,None),phase1_sub_ps) in
    let phase1_sub_contr = Unchecked.coh_to_sub_ps phase1 in
    (* Phase 2 *)
    let phase2_sub_contr = [(sqmm 0,true);(sqb 0,false)] in
    (* Phase 3 *)
    let phase3_sub_ps = sqb_sub_ps 0 in
    let phase3_sub,_ = Unchecked.sub_ps_to_sub phase3_sub_ps (Builtin.ps_comp 2) in
    let phase3 = Coh(Coh.check_inv (Builtin.ps_comp 2) unbias biasr ("builtin_biasr",0,None),phase3_sub_ps) in
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
    let phase1 = Coh(Coh.check_inv (Builtin.ps_comp 3) assocl assocr ("builtin_assoc",0,None),phase1_sub_ps) in
    let phase1_sub_contr = Unchecked.coh_to_sub_ps phase1 in
    (* Phase 2 *)
    let phase2_sub_ps = [(sqmm 1,true);(sqb 1,false);(sqt 1,false);(sqbr 1,false);(sqtm 0,true);(sqtr 0,false);(sqtl 0,false)] in
    let phase2 = Coh(Functorialisation.whisk 0 0 1, phase2_sub_ps) in
    let phase2_sub_contr = [(phase2,true);(comp_binary (sqtl 0) (sqtr 0) (sqtm 0) (sqbr 1) (sqb 1),false)] in
    (* Phase 3 *)
    let phase3_sub_ps = List.concat [[(sqbm 1,true);(sqbr 1,false)];(sqt_sub_ps 0)] in
    let phase3_sub = Unchecked.list_to_db_level_sub (List.map fst phase3_sub_ps) in
    let phase3 = Coh(Coh.check_inv (Builtin.ps_comp 3) assocr assocl ("builtin_assoc_inv",0,None),phase3_sub_ps) in
    let phase3_sub_contr = [(phase3,true);(Unchecked.tm_apply_sub assocl phase3_sub,false)] in
    (* Phase 4 *)
    let phase4_sub_ps = [(sqbm 1,true);(sqbr 1,false);(sqmm 0,true);(sqb 0,false);(sqt 0,false);(sqbr 0,false);(sqtl 0,false)] in
    let phase4 = Coh(Functorialisation.whisk 0 1 0,phase4_sub_ps) in
    let phase4_sub_contr = [(phase4,true);(comp_binary (sqtl 0) (sqbr 0) (sqb 0) (sqbr 1) (sqbm 1),false)] in
    (* Phase 5 *)
    let phase5_sub_ps = List.concat [[(sqbm 1,true);(sqbr 1,false)];(sqb_sub_ps 0)] in
    let phase5_sub = Unchecked.list_to_db_level_sub (List.map fst phase5_sub_ps) in
    let phase5 = Coh(Coh.check_inv (Builtin.ps_comp 3) assocl assocr ("builtin_assoc",0,None),phase5_sub_ps) in
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
      (* Various biased composites *)
      let ps = Builtin.ps_comp (arity+1) in
      let unbiasl = comp_binary (comp_n_l 0) (comp_n_r (arity-1)) (comp_n_tm arity) (comp_n_r arity) (comp_n_m arity) in
      let unbiasr = comp_binary (comp_n_l 0) (comp_n_r 0) (comp_n_m 0) (comp_n_r arity) (comp_kn_tm 1 arity) in
      let biasl = comp_binary (comp_n_l 0) (comp_n_r (arity-1)) (comp_binary (comp_n_l 0) (comp_n_r (arity-2)) (comp_n_tm (arity-1)) (comp_n_r (arity-1)) (comp_n_m (arity-1))) (comp_n_r arity) (comp_n_m arity) in
      let biasr = comp_binary (comp_n_l 0) (comp_n_r 0) (comp_n_m 0) (comp_n_r arity) (comp_binary (comp_n_l 1) (comp_n_r (arity-1)) (comp_kn_tm 1 (arity-1)) (comp_n_r arity) (comp_n_m arity)) in
      let sqb_corner_sub_ps = sqb_corner_comp_sub_ps (arity-1) in
      let sqb_corner_sub = fst (Unchecked.sub_ps_to_sub sqb_corner_sub_ps ps) in
      (* Phase 1 *)
      let phase1 = Coh(Coh.check_inv ps unbiasl biasl ("builtin_bias_left",0,None), sqt_corner_comp_sub_ps (arity-1)) in
      (* Phase 2 *)
      let phase2_presub = [sqmm (arity-1);sqbm (arity-1);sqtm (arity-1);sqmr (arity-1);sqbr (arity-1);sqtr (arity-1);sq_ind;sqb_comp (arity-1);sqt_comp (arity-1);sqml (arity-1);sqbl (arity-1);sqtl (arity-1);sqml 0;sqbl 0;sqtl 0] in
      let phase2_sub = Unchecked.list_to_db_level_sub phase2_presub in
      let phase2 = Unchecked.tm_apply_sub ccomp_binary phase2_sub in
      let phase2_tgt = Unchecked.tm_apply_sub biasr sqb_corner_sub in
      (* Phase 3 *)
      let phase3 = Coh(Coh.check_inv ps biasr unbiasr ("builtin_bias_right",0,None), sqb_corner_sub_ps) in
      let phase3_tgt = Unchecked.tm_apply_sub unbiasr sqb_corner_sub in
      (* Merge *)
      let comp_sub = List.concat [[(phase3,true);(phase3_tgt,false);(phase2,true);(phase2_tgt,false)];(Unchecked.coh_to_sub_ps phase1)] in
      Coh(Suspension.coh (Some(1)) (Builtin.comp_n 3), comp_sub)
    end
and ccomp_n arity =
  Memo.find_ccomp arity build_ccomp_n

(* Interchange needed for source of depth-1 non-inv coh *)
(*
https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXHBhcnRpYWxcXEdhbW1hIl0sWzIsMSwiXFxvdmVycmlnaHRhcnJvd3tcXHBhcnRpYWxcXEdhbW1hfV57WF9cXHRhdX0iXSxbMCwzLCJcXEdhbW1hIl0sWzAsMSwiXFxHYW1tYV57cmVkfSJdLFsxLDIsIlxcRGVsdGEiXSxbMSwzLCJcXFBoaSJdLFszLDIsIlxcRGVsdGFee3JlZH0iXSxbMSw0LCJcXG92ZXJyaWdodGFycm93e1xcR2FtbWF9XlgiXSxbMCwxLCJcXHNpZ21hIl0sWzAsMiwiXFx0YXUiLDEseyJsYWJlbF9wb3NpdGlvbiI6NzAsImN1cnZlIjo1fV0sWzMsMiwiXFxyaG9fXFxHYW1tYSIsMl0sWzAsMywiXFx0YXVfciIsMV0sWzEsNCwial8yIiwxXSxbMyw0LCJqXzEiLDFdLFs0LDAsIiIsMCx7InN0eWxlIjp7Im5hbWUiOiJjb3JuZXIifX1dLFs0LDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDUsImlfMSIsMV0sWzEsNSwiaV8yIiwxXSxbNSwwLCIiLDEseyJzdHlsZSI6eyJuYW1lIjoiY29ybmVyIn19XSxbNiw0LCJcXHJob19cXERlbHRhIiwxLHsiY3VydmUiOjF9XSxbMiw3XSxbMSw3LCJcXG92ZXJyaWdodGFycm93e1xcdGF1fV5YIiwxLHsiY3VydmUiOi0zfV0sWzUsNywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
 *)
let depth1_interchanger_src coh l ctxf =
  (* Setup *)
  let gamma,coh_ty,name = Coh.forget coh in
  let d = Unchecked.dim_ps gamma in
  (* Construct preimage locations *)
  let bdry = Unchecked.ps_bdry gamma in
  let tau = Unchecked.ps_tgt gamma in
  let _,bdry_c = Unchecked.sub_ps_to_sub tau bdry in
  let l_tau = Functorialisation.find_places bdry_c tau l in
  (* Construct ps_bdry_f *)
  let bdry_f_ctx = Functorialisation.ctx bdry_c l_tau in
  let bdry_f_db = Unchecked.db_level_sub_inv bdry_f_ctx in
  let bdry_f = PS.forget (PS.mk (Ctx.check bdry_f_ctx)) in
  let tau_f = Functorialisation.sub tau l ctxf in
  (* Construct composite context *)
  let phi,i1_ps,i2_ps = Unchecked.ps_compose (d-1) gamma bdry_f in
  let i1,_ = Unchecked.sub_ps_to_sub i1_ps gamma in
  let i2,_ = Unchecked.sub_ps_to_sub i2_ps bdry_f in
  (* Construct source (t[i1]) * (tgt_f[i2]) *)
  let src,tgt,ty_base = Coh.noninv_srctgt coh in
  let tgt_f_ty = Functorialisation.ty ty_base l_tau tgt bdry_c in
  let tgt_f_ty = Unchecked.ty_apply_sub (Unchecked.ty_apply_sub tgt_f_ty bdry_f_db) i2 in
  let tgt_f = Functorialisation.tm_one_step_tm tgt l_tau bdry_f_ctx in
  let tgt_f = Unchecked.tm_apply_sub (Unchecked.tm_apply_sub tgt_f bdry_f_db) i2 in
  let coh_src_sub_ps = Functorialisation.whisk_sub_ps 0 (Coh(coh,i1_ps)) (Unchecked.ty_apply_sub coh_ty i1) tgt_f tgt_f_ty in
  let coh_src = Coh(Functorialisation.whisk (d-1) 0 0,coh_src_sub_ps) in
  let _ = check_term (Ctx.check (Unchecked.ps_to_ctx phi)) coh_src in
  (* Construct reduced context *)
  let gamma_red = Ps_reduction.reduce (d-1) gamma in
  let delta,_,_ = Unchecked.ps_compose (d-1) gamma_red bdry_f in
  let delta_red = Ps_reduction.reduce (d-1) delta in
  let rho_delta = Ps_reduction.reduction_sub delta in
  (* Construct biased reduction sub from phi to delta_red *)
  let rho_gamma_i1 = Unchecked.sub_ps_apply_sub (Ps_reduction.reduction_sub gamma) i1 in
  let delta_ind = Unchecked.pullback_up (d-1) gamma_red bdry_f rho_gamma_i1 i2_ps in
  (* Construct target (comp delta_red src tgt) *)
  let coh_tgt_coh = Coh.check_noninv delta_red src tgt ((Unchecked.full_name name)^"_red",0,None) in
  let coh_tgt_sub_ps = Unchecked.sub_ps_apply_sub rho_delta (fst (Unchecked.sub_ps_to_sub delta_ind delta)) in
  let coh_tgt = Coh(coh_tgt_coh, coh_tgt_sub_ps) in
  let _ = check_term (Ctx.check (Unchecked.ps_to_ctx phi)) coh_tgt in
  (* Construct map into pullback *)
  let phi_ind_sub_ps = Unchecked.pullback_up (d-1) gamma bdry_f (Unchecked.identity_ps gamma) tau_f in
  let phi_ind,_ = Unchecked.sub_ps_to_sub phi_ind_sub_ps phi in
  (* Construct final coherence *)
  let intch_coh = Coh.check_inv phi coh_src coh_tgt ("intch_src",0,None) in
  let _,intch_ty,_ = Coh.forget intch_coh in
  let intch = Coh(intch_coh,phi_ind_sub_ps) in
  let _ = check_term (Ctx.check ctxf) intch in
  intch, Unchecked.ty_apply_sub intch_ty phi_ind
(*
https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXHBhcnRpYWxcXEdhbW1hIl0sWzIsMSwiXFxvdmVycmlnaHRhcnJvd3tcXHBhcnRpYWxcXEdhbW1hfV57WF9cXHRhdX0iXSxbMCwzLCJcXEdhbW1hIl0sWzAsMSwiXFxHYW1tYV57cmVkfSJdLFsxLDIsIlxcRGVsdGEiXSxbMSwzLCJcXFBoaSJdLFszLDIsIlxcRGVsdGFee3JlZH0iXSxbMSw0LCJcXG92ZXJyaWdodGFycm93e1xcR2FtbWF9XlgiXSxbMCwxLCJcXHNpZ21hIl0sWzAsMiwiXFx0YXUiLDEseyJsYWJlbF9wb3NpdGlvbiI6NzAsImN1cnZlIjo1fV0sWzMsMiwiXFxyaG9fXFxHYW1tYSIsMl0sWzAsMywiXFx0YXVfciIsMV0sWzEsNCwial8yIiwxXSxbMyw0LCJqXzEiLDFdLFs0LDAsIiIsMCx7InN0eWxlIjp7Im5hbWUiOiJjb3JuZXIifX1dLFs0LDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDUsImlfMSIsMV0sWzEsNSwiaV8yIiwxXSxbNSwwLCIiLDEseyJzdHlsZSI6eyJuYW1lIjoiY29ybmVyIn19XSxbNiw0LCJcXHJob19cXERlbHRhIiwxLHsiY3VydmUiOjF9XSxbMiw3XSxbMSw3LCJcXG92ZXJyaWdodGFycm93e1xcdGF1fV5YIiwxLHsiY3VydmUiOi0zfV0sWzUsNywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
 *)
let depth1_interchanger_tgt coh l ctxf =
  (* Setup *)
  let gamma,coh_ty,name = Coh.forget coh in
  let d = Unchecked.dim_ps gamma in
  (* Construct preimage locations *)
  let bdry = Unchecked.ps_bdry gamma in
  let sigma = Unchecked.ps_src gamma in
  let _,bdry_c = Unchecked.sub_ps_to_sub sigma bdry in
  let l_sigma = Functorialisation.find_places bdry_c sigma l in
  (* Construct ps_bdry_f *)
  let bdry_f_ctx = Functorialisation.ctx bdry_c l_sigma in
  let bdry_f_db = Unchecked.db_level_sub_inv bdry_f_ctx in
  let bdry_f = PS.forget (PS.mk (Ctx.check bdry_f_ctx)) in
  let sigma_f = Functorialisation.sub sigma l ctxf in
  (* Construct composite context *)
  let phi,i1_ps,i2_ps = Unchecked.ps_compose (d-1) bdry_f gamma in
  let i1,_ = Unchecked.sub_ps_to_sub i1_ps bdry_f in
  let i2,_ = Unchecked.sub_ps_to_sub i2_ps gamma in
  (* Construct target (src_f[i1]) * (t[i2]) *)
  let src,tgt,ty_base = Coh.noninv_srctgt coh in
  let src_f_ty = Functorialisation.ty ty_base l_sigma src bdry_c in
  let src_f_ty = Unchecked.ty_apply_sub (Unchecked.ty_apply_sub src_f_ty bdry_f_db) i1 in
  let src_f = Functorialisation.tm_one_step_tm src l_sigma bdry_f_ctx in
  let src_f = Unchecked.tm_apply_sub (Unchecked.tm_apply_sub src_f bdry_f_db) i1 in
  let coh_tgt_sub_ps = Functorialisation.whisk_sub_ps 0 src_f src_f_ty (Coh(coh,i2_ps)) (Unchecked.ty_apply_sub coh_ty i2) in
  let coh_tgt = Coh(Functorialisation.whisk (d-1) 0 0,coh_tgt_sub_ps) in
  let _ = check_term (Ctx.check (Unchecked.ps_to_ctx phi)) coh_tgt in
  (* Construct reduced context *)
  let gamma_red = Ps_reduction.reduce (d-1) gamma in
  let delta,_,_ = Unchecked.ps_compose (d-1) bdry_f gamma_red in
  let delta_red = Ps_reduction.reduce (d-1) delta in
  let rho_delta = Ps_reduction.reduction_sub delta in
  (* Construct biased reduction sub from phi to delta_red *)
  let rho_gamma_i2 = Unchecked.sub_ps_apply_sub (Ps_reduction.reduction_sub gamma) i2 in
  let delta_ind = Unchecked.pullback_up (d-1) bdry_f gamma_red i1_ps rho_gamma_i2 in
  (* Construct source (comp delta_red src tgt) *)
  let coh_src_coh = Coh.check_noninv delta_red src tgt ((Unchecked.full_name name)^"_red",0,None) in
  let coh_src_sub_ps = Unchecked.sub_ps_apply_sub rho_delta (fst (Unchecked.sub_ps_to_sub delta_ind delta)) in
  let coh_src = Coh(coh_src_coh, coh_src_sub_ps) in let _ = check_term (Ctx.check (Unchecked.ps_to_ctx phi)) coh_src in
  (* Construct map into pullback *)
  let phi_ind_sub_ps = Unchecked.pullback_up (d-1) bdry_f gamma sigma_f (Unchecked.sub_ps_apply_sub (Unchecked.identity_ps gamma) (Functorialisation.tgt_subst l)) in
  let phi_ind,_ = Unchecked.sub_ps_to_sub phi_ind_sub_ps phi in
  (* Construct final coherence *)
  let intch_coh = Coh.check_inv phi coh_src coh_tgt ("intch_tgt",0,None) in
  let _,intch_ty,_ = Coh.forget intch_coh in
  let intch = Coh(intch_coh,phi_ind_sub_ps) in
  let _ = check_term (Ctx.check ctxf) intch in
  intch, Unchecked.ty_apply_sub intch_ty phi_ind

let rec depth1_bridge_sub src_sub tgt_sub l ctxf =
  match src_sub,tgt_sub with
  | [],[] -> []
  | (src,expl)::src_tl,(tgt,_)::tgt_l ->
    begin
      let rest = depth1_bridge_sub src_tl tgt_l l ctxf in
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
        let linear_ps,_,_ = Coh.forget (Builtin.comp_n arity) in
        let linear_ctx = Unchecked.ps_to_ctx linear_ps in
        let linear_ctxf = Functorialisation.ctx linear_ctx (List.map fst linear_ctx) in
        let _ = check_term (Ctx.check linear_ctxf) (Unchecked.tm_apply_sub (ccomp_n arity) (Unchecked.db_level_sub linear_ctxf)) in
        let ccomp = Suspension.tm (Some(d-1)) (ccomp_n arity) in
        let inner_subf = Functorialisation.sub inner_sub l ctxf in
        let inner_subf_norm = Unchecked.list_to_db_level_sub (List.map fst inner_subf) in
        let bridge = Unchecked.tm_apply_sub ccomp inner_subf_norm in
        let _ = check_term (Ctx.check ctxf) bridge in
        (bridge,expl)::(tgt,false)::(src,false)::rest
    end
  | _,_ -> assert false

let init () =
    begin
        Functorialisation.cubical_comp := ccomp_n;
        Functorialisation.depth1_interchanger_src := depth1_interchanger_src;
        Functorialisation.depth1_interchanger_tgt := depth1_interchanger_tgt;
        Functorialisation.depth1_bridge_sub := depth1_bridge_sub;
    end
