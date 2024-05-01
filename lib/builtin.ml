open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

module Memo = struct
  let tbl = Hashtbl.create 97
  let tbl_whisk = Hashtbl.create 97

  let find i f =
    try Hashtbl.find tbl i with
    | Not_found ->
      let res = f i in
      Hashtbl.add tbl i res;
      res

  let find_whisk i f =
    try Hashtbl.find tbl_whisk i with
    | Not_found ->
      let res = f i in
      Hashtbl.add tbl_whisk i res;
      res

  let id =
    check_coh (Br[]) (Arr(Obj,Var(Db 0),Var(Db 0))) ("builtin_id", 0, None)
end

let rec ps_comp i =
  match i with
  | i when i <= 0 -> Error.fatal "builtin composition with less than 0 argument"
  | i when i = 1 -> Br [Br[]]
  | i ->
    match ps_comp (i-1) with
    | Br l -> Br (Br[] :: l)

let comp_n arity =
  let build_comp i =
    let ps = ps_comp i in
    Coh.check_noninv ps (Var (Db 0)) (Var(Db 0)) ("builtin_comp", 0, None)
  in
  Memo.find arity build_comp

let arity_comp s =
  let n = List.length s in
  if !Settings.explicit_substitutions then
    (n-1)/2
  else n

let comp s =
  let arity = arity_comp s in
  comp_n arity

(* returns the n-composite of a (n+j)-cell with a (n+k)-cell *)
let whisk n j k =
  let build_whisk t =
    let n,j,k = t in
    let comp = comp_n 2 in
    let func_data = [k;j] in
    Suspension.coh (Some(n)) (Functorialisation.coh comp func_data)
  in
  Memo.find_whisk (n,j,k) build_whisk

(*
  How long should substitutions for whisk be?
  (whisk 0 0 0) requires ps-context (x(f)y(g)z) so 2+1+1+1
  (whisk n 0 0) requires 2*(n+1)+1+1+1
  (whisk n j 0) requires (2*(n+1))+((2*j)+1)+1+1
  (whisk n 0 k) requires (2*(n+1))+1+(2*k+1)+1

  Assuming ty1 has right dimension, we just need to know k
*)
let whisk_sub_ps k t1 ty1 t2 ty2 =
    let rec take n l =
        match l with
        | h::t when n > 0 -> h::(take (n-1) t)
        | _ -> [] in
    let sub_base = Unchecked.ty_to_sub_ps ty1 in
    let sub_ext = take (2*k+1) (Unchecked.ty_to_sub_ps ty2) in
    List.concat [[(t2,true)];sub_ext;[(t1,true)];sub_base]

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

let id = Memo.id

let id_all_max ps =
  let d = Unchecked.dim_ps ps in
  let rec id_map l =
    let t = Var (Db 0) in
    match l with
    | [] -> [t, false]
    | Br[]::l -> (Coh(id, [t,true]), true)::(t,false)::(id_map l)
    | _ -> Error.fatal "identity must be inserted on maximal argument"
  in
  let rec aux i ps =
    match i,ps with
    | _, Br [] -> [Var (Db 0), true]
    | 0, Br l -> id_map l
    | i, Br l -> Unchecked.suspwedge_subs_ps
                   (List.map (aux (i-1)) l)
                   (List.map (Unchecked.ps_bdry) l)
  in
  aux (d-1) ps

let unbiased_unitor ps t =
  let bdry =  Unchecked.ps_bdry ps in
  let src =
    let coh = Coh.check_noninv ps t t ("endo",0,None) in
    Coh(coh, id_all_max ps)
  in
  let
    a = Ty.forget (Tm.typ (check_term (Ctx.check (Unchecked.ps_to_ctx bdry)) t))
  in
  let da = Unchecked.dim_ty a in
  let sub_base = Unchecked.ty_to_sub_ps a in
  let tgt = Coh (Suspension.coh (Some da) id, (t,true)::sub_base) in
  Coh.check_inv bdry src tgt ("unbiased_unitor",0,None)

(* returns the associator pairing up the middle two cells of a composite of
    (2*k) 1-cells. The argument is the integer k *)
let middle_associator k =
  let ps = ps_comp (2*k) in
  let src = Coh(comp_n (2*k), Unchecked.(identity_ps ps)) in
  let tgt =
    let sub_assoc_middle =
      let rec compute_sub i =
        match i with
        | i when i <= 0 -> [Var(Db 0), false]
        | i when i < k ->
            (Var (Db (2*i)), true)::
            (Var (Db (2*i-1)), false)::
            (compute_sub (i-1))
        | i when i = k ->
            let sub_comp =
              [ Var (Db (2*k+2)),true;
                Var (Db (2*k+1)), false;
                Var (Db (2*k)), true;
                Var (Db (2*k-1)), false;
                Var (Db (2*k-3)), false]
            in
            let comp = (Coh(comp_n 2, sub_comp)) in
            (comp, true)::(Var (Db (2*k+1)), false)::(compute_sub (k-1))
        | i -> (Var (Db (2*i+2)), true)::
               (Var (Db (2*i+1)), false)::
               (compute_sub (i-1))
      in
      compute_sub (2*k-1)
    in
    Coh(comp_n (2*k-1), sub_assoc_middle)
  in
  Coh.check_inv ps src tgt ("focus", 0, None)

(* returns the unitor cancelling the identity in the middle of a composite of
(2*k+1) 1-cells. The argument is the integer k *)
let middle_unitor k =
  let ps = ps_comp (2*k) in
  let src =
    let sub_id_middle =
      let rec compute_sub i =
        match i with
        | i when i <= 0 -> [Var (Db  0), false]
        | i when i <= k ->
          (Var (Db (2*i)), true)::
          (Var (Db (2*i-1)), false)::
          (compute_sub (i-1))
        | i when i = k+1 ->
          let id = (Coh(id, [Var (Db (2*k-1)), false])) in
            (id, true)::(Var (Db (2*k-1)), false)::(compute_sub (k))
        | i -> (Var (Db (2*i-2)), true)::
               (Var (Db (2*i-3)), false)::
               (compute_sub (i-1))
      in
      compute_sub (2*k+1)
    in
    Coh(comp_n (2*k+1), sub_id_middle) in
  let tgt = Coh(comp_n (2*k), Unchecked.(identity_ps ps)) in
  Coh.check_inv ps src tgt ("unit", 0, None)

(* returns the whiskering rewriting the middle term of a composite of (2*k+1)
    1-cells. The argument is the integer k *)
let middle_rewrite k =
  let comp = comp_n (2*k+1) in
  let func_data =
    List.concat [(List.init k (fun _ -> 0)); [1]; (List.init k (fun _ -> 0))] in
  Functorialisation.coh comp func_data

let () = Functorialisation.builtin_comp := comp_n
let () = Functorialisation.builtin_whisk := whisk
let () = Functorialisation.builtin_whisk_sub_ps := whisk_sub_ps

