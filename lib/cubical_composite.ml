open Builtin
open Kernel
open Unchecked_types.Unchecked_types(Coh)
(*
https://q.uiver.app/#q=WzAsNCxbMCwwLCIwIl0sWzIsMCwiMyJdLFsyLDIsIjQiXSxbMCwyLCIxIl0sWzEsMiwiNSIsMV0sWzAsMywiMiIsMV0sWzMsMSwiOCIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sImxldmVsIjoyfV0sWzAsMSwiNiIsMV0sWzMsMiwiNyIsMV0sWzMsMiwiNyIsMSx7ImN1cnZlIjozfV0sWzAsMSwiNiIsMSx7ImN1cnZlIjotM31dLFs5LDgsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbNywxMCwiIiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==
*)

let tdb i = Var (Db i)
let comp_n_l n = if n = 0 then tdb 0 else tdb ((2*n)-1)
let comp_n_r n = tdb ((2*n)+1)
let comp_n_m n = tdb ((2*n)+2)
let rec comp_kn_sub_ps k n = if n = 0 then [(comp_n_m k,true);(comp_n_r k,false);(comp_n_l k,false)] else (comp_n_m (k+n),true)::(comp_n_r (k+n),false)::(comp_kn_sub_ps k (n-1))
let _comp_n_sub_ps n = comp_kn_sub_ps 0 n
let comp_kn_tm k n = Coh(comp_n n, comp_kn_sub_ps k (n-1))
let comp_n_tm n = comp_kn_tm 0 n
let comp_unary x y f = Coh(comp_n 1, [(f,true);(y,false);(x,false)])
let comp_binary x y f z g = Coh(comp_n 2, [(g,true);(z,false);(f,true);(y,false);(x,false)])
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
let sqb n = Coh(comp_n 2, sqb_sub_ps n)
let sqt n = Coh(comp_n 2, sqt_sub_ps n)
let rec sqb_comp_sub_ps n = if n = 0 then [(sqbm 0,true);(sqbr 0,false);(sqbl 0,false)] else (sqbm n,true)::(sqbr n,false)::(sqb_comp_sub_ps (n-1))
let rec sqt_comp_sub_ps n = if n = 0 then [(sqtm 0,true);(sqtr 0,false);(sqtl 0,false)] else (sqtm n,true)::(sqtr n,false)::(sqt_comp_sub_ps (n-1))
let sqb_comp n = Coh(comp_n n, sqb_comp_sub_ps (n-1))
let sqt_comp n = Coh(comp_n n, sqt_comp_sub_ps (n-1))
let rec sqb_corner_comp_sub_ps n = if n = 0 then (sqb_sub_ps 0) else (sqbm n,true)::(sqbr n,false)::(sqb_corner_comp_sub_ps (n-1))
let sqt_corner_comp_sub_ps n = (sqmr n,true)::(sqbr n,false)::(sqtm n,true)::(sqtr n,false)::(if n>0 then (sqt_comp_sub_ps (n-1)) else [])

let ccomp_unary =
    let unbias = comp_n_tm 2 in
    let biasl = comp_binary (tdb 0) (tdb 1) (comp_unary (tdb 0) (tdb 1) (tdb 2)) (tdb 3) (tdb 4) in
    let biasr = comp_binary (tdb 0) (tdb 1) (tdb 2) (tdb 3) (comp_unary (tdb 1) (tdb 3) (tdb 4)) in
    (* Phase 1 *)
    let phase1_sub_ps = sqb_sub_ps 0 in
    let phase1_sub = Unchecked.list_to_db_level_sub (List.map fst phase1_sub_ps) in
    let phase1 = Coh(Coh.check_inv (ps_comp 2) biasr unbias ("builtin_unbiasor",0,None),phase1_sub_ps) in
    let phase1_sub_contr = [(phase1,true);(Unchecked.tm_apply_sub unbias phase1_sub,false);(Unchecked.tm_apply_sub biasr phase1_sub,false);(sqbr 0,false);(sqtl 0,false)] in
    (* Phase 3 *)
    let phase3_sub_ps = sqt_sub_ps 0 in
    let phase3_sub = Unchecked.list_to_db_level_sub (List.map fst phase3_sub_ps) in
    let phase3 = Coh(Coh.check_inv (ps_comp 2) unbias biasl ("builtin_biasor",0,None),phase3_sub_ps) in
    let phase3_sub_contr = [(phase3,true);(Unchecked.tm_apply_sub biasl phase3_sub,false)] in
    (* Phase 2 *)
    let phase2_sub_contr = [(tdb 8,true);(Unchecked.tm_apply_sub unbias phase3_sub,false)] in
    (* Collate *)
    let comp_sub = List.concat [phase3_sub_contr;phase2_sub_contr;phase1_sub_contr] in
    let comp = Suspension.coh (Some(1)) (comp_n 3) in
    Coh(comp,comp_sub)

(*
https://q.uiver.app/#q=WzAsOSxbMCwxLCIwIl0sWzIsMSwiMyJdLFsyLDMsIjQiXSxbMCwzLCIxIl0sWzQsMSwiOSJdLFs0LDMsIjEwIl0sWzAsMCwiMCJdLFsyLDAsIjEiXSxbNCwwLCIzIl0sWzAsMSwiNiIsMV0sWzEsMiwiNSIsMV0sWzAsMywiMiIsMV0sWzMsMiwiNyIsMV0sWzEsNCwiMTIiLDFdLFs0LDUsIjExIiwxXSxbMiw1LCIxMyIsMV0sWzYsNywiMiIsMV0sWzcsOCwiNCIsMV0sWzMsMSwiOCIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sImxldmVsIjoyfV0sWzIsNCwiMTQiLDEseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9LCJsZXZlbCI6Mn1dXQ==
*)

let ccomp_binary =
    let assocr = comp_binary (tdb 0) (tdb 1) (tdb 2) (tdb 5) (comp_binary (tdb 1) (tdb 3) (tdb 4) (tdb 5) (tdb 6)) in
    let assocl = comp_binary (tdb 0) (tdb 3) (comp_n_tm 2) (tdb 5) (tdb 6) in
    (* Phase 1 *)
    let phase1_sub_ps = List.concat [[(sqbm 1,true);(sqbr 1,false)];(sqb_sub_ps 0)] in
    let phase1_sub = Unchecked.list_to_db_level_sub (List.map fst phase1_sub_ps) in
    let phase1 = Coh(Coh.check_inv (ps_comp 3) assocr assocl ("builtin_assoc",0,None),phase1_sub_ps) in
    let phase1_sub_contr = [(phase1,true);(Unchecked.tm_apply_sub assocl phase1_sub,false);(Unchecked.tm_apply_sub assocr phase1_sub,false);(sqbr 1,false);(sqtl 0,false)] in
    (* Phase 2 *)
    let phase2_sub_ps = [(sqbm 1,true);(sqbr 1,false);(sqmm 0,true);(sqt 0,false);(sqb 0,false);(sqbr 0,false);(sqtl 0,false)] in
    let phase2 = Coh(whisk 0 1 0,phase2_sub_ps) in
    let phase2_sub_contr = [(phase2,true);(comp_binary (sqtl 0) (sqbr 0) (sqt 0) (sqbr 1) (sqbm 1),false)] in
    (* Phase 3 *)
    let phase3_sub_ps = List.concat [[(sqbm 1,true);(sqbr 1,false)];(sqt_sub_ps 0)] in
    let phase3_sub = Unchecked.list_to_db_level_sub (List.map fst phase3_sub_ps) in
    let phase3 = Coh(Coh.check_inv (ps_comp 3) assocl assocr ("builtin_assoc_inv",0,None),phase3_sub_ps) in
    let phase3_sub_contr = [(phase3,true);(Unchecked.tm_apply_sub assocr phase3_sub,false)] in
    (* Phase 4 *)
    let phase4_sub_ps = [(sqmm 1,true);(sqt 1,false);(sqb 1,false);(sqbr 1,false);(sqtm 0,true);(sqtr 0,false);(sqtl 0,false)] in
    let phase4 = Coh(whisk 0 0 1, phase4_sub_ps) in
    let phase4_sub_contr = [(phase4,true);(comp_binary (sqtl 0) (sqtr 0) (sqtm 0) (sqbr 1) (sqt 1),false)] in
    (* Phase 5 *)
    let phase5_sub_ps = [(sqmr 1,true);(sqbr 1,false);(sqtm 1,true);(sqtr 1,false);(sqtm 0,true);(sqtr 0,false);(sqtl 0,false)] in
    let phase5_sub = Unchecked.list_to_db_level_sub (List.map fst phase5_sub_ps) in
    let phase5 = Coh(Coh.check_inv (ps_comp 3) assocr assocl ("builtin_assoc",0,None),phase5_sub_ps) in
    let phase5_sub_contr = [(phase5,true);(Unchecked.tm_apply_sub assocl phase5_sub,false);] in
    (* Merge *)
    let comp_sub = List.concat [phase5_sub_contr;phase4_sub_contr;phase3_sub_contr;phase2_sub_contr;phase1_sub_contr] in
    let comp = Suspension.coh (Some(1)) (comp_n 5) in
    Coh(comp,comp_sub)

let rec ccomp_ind arity =
    if arity = 2 then
        ccomp_binary
    else
        let sq_ind = ccomp_ind (arity-1) in
        let ps = ps_comp (arity+1) in
        let unbiasl = comp_binary (comp_n_l 0) (comp_n_r (arity-1)) (comp_n_tm arity) (comp_n_r arity) (comp_n_m arity) in
        let unbiasr = comp_binary (comp_n_l 0) (comp_n_r 0) (comp_n_m 0) (comp_n_r arity) (comp_kn_tm 1 arity) in
        let biasl = comp_binary (comp_n_l 0) (comp_n_r (arity-1)) (comp_binary (comp_n_l 0) (comp_n_r (arity-2)) (comp_n_tm (arity-1)) (comp_n_r (arity-1)) (comp_n_m (arity-1))) (comp_n_r arity) (comp_n_m arity) in
        let biasr = comp_binary (comp_n_l 0) (comp_n_r 0) (comp_n_m 0) (comp_n_r arity) (comp_binary (comp_n_l 1) (comp_n_r (arity-1)) (comp_kn_tm 1 (arity-1)) (comp_n_r arity) (comp_n_m arity)) in
        let sqb_corner_sub_ps = sqb_corner_comp_sub_ps (arity-1) in
        let sqt_corner_sub_ps = sqt_corner_comp_sub_ps (arity-1) in
        let sqb_corner_sub = fst (Unchecked.sub_ps_to_sub sqb_corner_sub_ps ps) in
        let sqt_corner_sub = fst (Unchecked.sub_ps_to_sub sqt_corner_sub_ps ps) in
        (* Phase 1 *)
        let phase1 = Coh(Coh.check_inv ps unbiasr biasr ("builtin_bias",0,None), sqb_corner_sub_ps) in
        let phase1_src = Unchecked.tm_apply_sub unbiasr sqb_corner_sub in
        let phase1_tgt = Unchecked.tm_apply_sub biasr sqb_corner_sub in
        (* Phase 2 *)
        let phase2_presub = [sqmm (arity-1);sqbm (arity-1);sqtm (arity-1);sqmr (arity-1);sqbr (arity-1);sqtr (arity-1);sq_ind;sqb_comp (arity-1);sqt_comp (arity-1);sqml (arity-1);sqbl (arity-1);sqtl (arity-1);sqml 0;sqbl 0;sqtl 0] in
        let phase2_sub = Unchecked.list_to_db_level_sub phase2_presub in
        let phase2 = Unchecked.tm_apply_sub ccomp_binary phase2_sub in
        let phase2_tgt = Unchecked.tm_apply_sub biasl sqt_corner_sub in
        (* Phase 3 *)
        let phase3 = Coh(Coh.check_inv ps biasl unbiasl ("builtin_bias",0,None), sqt_corner_sub_ps) in
        let phase3_tgt = Unchecked.tm_apply_sub unbiasl sqt_corner_sub in
        (* Merge *)
        let comp_sub = [(phase3,true);(phase3_tgt,false);(phase2,true);(phase2_tgt,false);(phase1,true);(phase1_tgt,false);(phase1_src,false);(sqbr (arity-1),false);(sqtl 0,false)] in
        let _ = Unchecked.sub_ps_to_sub comp_sub (Unchecked.suspend_ps (ps_comp 3)) in
        Coh(Suspension.coh (Some(1)) (comp_n 3), comp_sub)

let ccomp_n arity =
    match arity with
    | 1 -> ccomp_unary
    | _ -> ccomp_ind arity

let ccomp s =
  let arity = arity_comp s in
  ccomp_n arity

let init () = Functorialisation.builtin_ccomp :=  ccomp_n
