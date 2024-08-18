open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

let tdb i = Var(Db i)
let wcomp = Functorialisation.wcomp

let rec bdry n ty =
  match ty, n with
  | Arr(b,s,t), 0 -> b,s,t
  | Arr(b,_,_), _ -> bdry (n-1) b
  | _, _ -> assert false

let src n ty = let b,s,_ = bdry n ty in s,b
let tgt n ty = let b,_,t = bdry n ty in t,b

let cone_tmty f fty l p =
  let fcty = Cones.cone_ty f fty l p in
  let fc = Cones.cone_tm f l p in
  fc, fcty

let src_cone n ty l p =
  let s, b = src n ty in
  cone_tmty s b l p

(* Unchecked method to unwrap n(n-1)n composites *)
let unwrap_composite_lr t ty =
  let (ps,_,_),s = match t with
  | Coh(c,s) -> Coh.forget c,s
  | _ -> assert false in
  let len = List.length s in
  let d = Unchecked.dim_ps ps in
  let left,_ = List.nth s (len-(2*d)-1) in
  let right,_ = List.nth s (len-(2*d+2)-1) in
  let rl,_ = List.nth s (len-(2*d-1)-1) in
  let b,ll,rr = bdry 0 ty in
  left, Arr(b,ll,rl), right, Arr(b,rl,rr)

(* Super unchecked method to reassociate nested binary composites
   Matches f * (g * h) and constructs sub out of (x(f)y(g)z)
   (f * g) * h -> f * (g * h)
*)
let assoc_right_sub t ty =
  let a, aty, inner, inner_ty = unwrap_composite_lr t ty in
  let b, bty, c, cty = unwrap_composite_lr inner inner_ty in
  (c,true)::(fst (tgt 0 cty),false)
  ::(b,true)::(fst (tgt 0 bty),false)
  ::(a,true)::(Unchecked.ty_to_sub_ps aty)

let reassoc_forward t ty =
  let d = Unchecked.dim_ty ty in
  let assoc = Suspension.coh (Some(d-1)) (Builtin.assoc) in
  let sub = assoc_right_sub t ty in
  Unchecked.coh_ty assoc sub

let reassoc_backward t ty =
  let d = Unchecked.dim_ty ty in
  let assoc = Suspension.coh (Some(d-1)) (Inverse.coh (Builtin.assoc)) in
  let sub = assoc_right_sub t ty in
  Unchecked.coh_ty assoc sub

let phase_n0 f fty g gty l p =
  let d = Unchecked.dim_ty fty in
  let fc = (Cones.cone_tm f l p,Cones.cone_ty f fty l p) in
  let gc = (Cones.cone_tm g l p,Cones.cone_ty g gty l p) in
  let h = if d<2 then g, gty else tgt (d-2) gty in
  wcomp gc 1 (wcomp fc 0 h)

let phase_01 f fty g gty l p =
  let x,_ = src 0 fty in
  let _,y,z = bdry 0 gty in
  let xc = Cones.cone_tm x l p in
  let sub_ps = [g,true;z,false;f,true;y,false;xc,true;x,false;Var(p),false] in
  Unchecked.coh_ty Builtin.assoc sub_ps

let assoc_conj m mty =
  (* Part 2 *)
  let part2b,part2s,part2t = bdry 0 mty in
  (* Part 1 *)
  let part1, part1ty = reassoc_forward part2s part2b in
  (* Part 3 *)
  let part3, part3ty = reassoc_backward part2t part2b in
  let part3t,_ = tgt 0 part3ty in
  (* Collate *)
  let comp = Suspension.coh (Some(2)) (Builtin.comp_n 3) in
  let sub = (part3,true)::(part3t,false)::(m,true)::(part2t,false)::(part1,true)::(Unchecked.ty_to_sub_ps part1ty) in
  Unchecked.coh_ty comp sub

let nat_of_phase a aty b bty l p ph =
  (* Setup *)
  let fty,fs,ft = bdry 0 aty in
  let gty,gs,gt = bdry 0 bty in
  let r, _ = ph fs fty gs gty l p in
  let v1,v2 = match fs,gs with
  | Var(v1),Var(v2) -> v1,v2
  | _, _ -> assert false in
  (* Compute nat *)
  let nat = Inverse.compute_inverse (Functorialisation.tm_one_step_tm r [v2;v1]) in
  let nat_sub = [Var.Bridge(v2),b;Var.Plus(v2),gt;Bridge(v1),a;Plus(v1),ft] in
  match nat with
  | Coh(c,s) -> Unchecked.coh_ty c (Unchecked.sub_ps_apply_sub s nat_sub)
  | _ -> assert false

let phase_of_nat a aty b bty c cty l p ph =
  let d = Unchecked.dim_ty cty in
  let nat = nat_of_phase a aty b bty l p ph in
  let middle, middlety = wcomp (c,cty) (d-1) nat in
  assoc_conj middle middlety

(*
  (a *_1 b) *_0 (c *_1 d) -> (a *_0 c) *_1 (b *_0 d)
*)
let intch_comp_1001_coh =
  let ps = Br[Br[Br[];Br[]];Br[Br[];Br[]]] in
  let fty = Arr(Obj,tdb 0,tdb 1) in
  let gty = Arr(Obj,tdb 1,tdb 7) in
  let a = tdb 4,Arr(fty,tdb 2,tdb 3) in
  let b = tdb 6,Arr(fty,tdb 3,tdb 5) in
  let c = tdb 10,Arr(gty,tdb 8,tdb 9) in
  let d = tdb 12,Arr(gty,tdb 9,tdb 11) in
  let s,_ = wcomp (wcomp a 1 b) 0 (wcomp c 1 d) in
  let t,_ = wcomp (wcomp a 0 c) 1 (wcomp b 0 d) in
  Coh.check_inv ps s t ("comp_1001_intch",0,[])

let intch_comp_2112_coh = Suspension.coh (Some(1)) (intch_comp_1001_coh)

let intch_comp_2112 m mty n nty p pty q qty =
  let p_sub = Unchecked.ty_to_sub_ps pty in
  let sub = (q,true)::(fst (tgt 0 qty),false)::(p,true)::(List.hd p_sub)::(List.nth p_sub 1)::(List.nth p_sub 2)::(n,true)::(fst (tgt 0 nty),false)::(m,true)::(Unchecked.ty_to_sub_ps mty) in
  Unchecked.coh_ty (intch_comp_2112_coh) sub

(*
  (a *_1 b) *_0 g -> (a *_0 g) *_1 (b *_0 g)
  https://q.uiver.app/#q=WzAsMyxbMCwwLCIwIl0sWzIsMCwiMSJdLFs0LDAsIjciXSxbMCwxLCIyIiwwLHsiY3VydmUiOi01fV0sWzAsMSwiNSIsMix7ImN1cnZlIjo1fV0sWzAsMSwiMyIsMV0sWzEsMiwiOCIsMV0sWzMsNSwiNCIsMix7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbNSw0LCI2IiwyLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==
*)
let intch_comp_10_coh =
  let ps = Br[Br[];Br[Br[];Br[]]] in
  let fty = Arr(Obj,tdb 0,tdb 1) in
  let g = tdb 8,Arr(Obj,tdb 1,tdb 7) in
  let a = tdb 4,Arr(fty,tdb 2,tdb 3) in
  let b = tdb 6,Arr(fty,tdb 3,tdb 5) in
  let s,_ = wcomp (wcomp a 1 b) 0 g in
  let t,_ = wcomp (wcomp a 0 g) 1 (wcomp b 0 g) in
  Coh.check_inv ps s t ("comp_10_intch",0,[])

let intch_comp_21_coh = Suspension.coh (Some(1)) (intch_comp_10_coh)

let _intch_comp_21 m mty n nty c cty =
  let sub = (c,true)::(fst (tgt 0 cty),false)::(n,true)::(fst (tgt 0 nty),false)::(m,true)::(Unchecked.ty_to_sub_ps mty) in
  Unchecked.coh_ty (intch_comp_21_coh) sub

(*
  Interchange (m *_2 n) *_0 g -> (m *_0 g) *_2 (n *_0 g)
  https://q.uiver.app/#q=WzAsMyxbMCwwLCIwIl0sWzIsMCwiMSJdLFs0LDAsIjkiXSxbMCwxLCIyIiwwLHsiY3VydmUiOi00fV0sWzAsMSwiMyIsMix7ImN1cnZlIjo0fV0sWzEsMiwiMTAiLDFdLFszLDQsIjQiLDIseyJvZmZzZXQiOjUsImN1cnZlIjoxLCJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzMsNCwiNyIsMCx7Im9mZnNldCI6LTUsImN1cnZlIjotMSwic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dLFszLDQsIjUiLDEseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzYsOCwiNiIsMCx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbOCw3LCI4IiwwLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==
*)
let intch_comp_20_coh =
  let ps = Br[Br[];Br[Br[Br[];Br[]]]] in
  let f = tdb 2,Arr(Obj,tdb 0,tdb 1) in
  let g = tdb 10,Arr(Obj,tdb 1,tdb 9) in
  let a,b,c,aty = tdb 4,tdb 5,tdb 7,Arr(snd f,fst f,tdb 3) in
  let m = tdb 6,Arr(aty,a,b) in
  let n = tdb 8,Arr(aty,b,c) in
  let s,_ = wcomp (wcomp m 2 n) 0 g in
  let t,_ = wcomp (wcomp m 0 g) 2 (wcomp n 0 g) in
  Coh.check_inv ps s t ("comp_20_intch",0,[])

let intch_comp_20 m mty n nty g gty =
  let sub = (g,true)::(fst (tgt 0 gty),false)::(n,true)::(fst (tgt 0 nty),false)::(m,true)::(Unchecked.ty_to_sub_ps mty) in
  Unchecked.coh_ty intch_comp_20_coh sub

(*
https://q.uiver.app/#q=WzAsMyxbMCwwLCIwIl0sWzIsMCwiMSJdLFs0LDAsIjYiXSxbMCwxLCIzIiwxXSxbMCwxLCI1IiwyLHsiY3VydmUiOjR9XSxbMSwyLCI3IiwwLHsiY3VydmUiOi0yfV0sWzEsMiwiOCIsMix7ImN1cnZlIjoyfV0sWzAsMSwiMiIsMCx7ImN1cnZlIjotNH1dLFszLDQsIjYiLDAseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzUsNiwiOSIsMCx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbNywzLCI0IiwwLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==
*)
let intch_phase_11_coh =
  let ps = Br[Br[Br[]];Br[Br[];Br[]]] in
  let f = tdb 2,Arr(Obj,tdb 0,tdb 1) in
  let g = tdb 8,Arr(Obj,tdb 1,tdb 7) in
  let g' = tdb 9,snd g in
  let a = tdb 4,Arr(snd f,tdb 2,tdb 3) in
  let b = tdb 6,Arr(snd f,tdb 3,tdb 5) in
  let c = tdb 10,Arr(snd g,tdb 8,tdb 9) in
  let s,_ = wcomp (wcomp f 0 c) 1 (wcomp (wcomp a 1 b) 0 g') in
  let t,_ = wcomp (wcomp a 0 g) 1 (wcomp b 0 c) in
  Coh.check_inv ps s t ("phase_11_intch",0,[])

let intch_phase_11 a aty b bty c cty =
  let c_sub = Unchecked.ty_to_sub_ps cty in
  let sub = (c,true)::(List.hd c_sub)::(List.nth c_sub 1)::(List.nth c_sub 2)::(b,true)::(fst (tgt 0 bty),false)::(a,true)::(Unchecked.ty_to_sub_ps aty) in
  Unchecked.coh_ty intch_phase_11_coh sub

let phase_11 a aty b bty l p =
  (* Setup *)
  let xc = src_cone 1 aty l p in
  let fc = src_cone 0 aty l p in
  let gc = src_cone 0 bty l p in
  let c = wcomp xc 0 (a,aty) in
  (* Core of the phase *)
  let intch = intch_phase_11 (fst fc) (snd fc) (fst c) (snd c) b bty in
  let middle, middlety = wcomp gc 1 intch in
  (* Conjugate by assoc *)
  assoc_conj middle middlety

let phase_21 m mty n nty l p =
  let g' = tgt 1 nty in
  let xc = src_cone 2 mty l p in
  let yc = src_cone 2 nty l p in
  let fc = src_cone 1 mty l p in
  let gc = src_cone 1 nty l p in
  let ac = src_cone 0 mty l p in
  let bc = src_cone 0 nty l p in
  (* Part 0 *)
  let t0 = begin
    let l = wcomp bc 2 (wcomp gc 1 (wcomp yc 0 (n,nty))) in
    let p, pty = wcomp fc 1 (wcomp xc 0 (m,mty)) in
    let intch = intch_comp_20 (fst ac) (snd ac) p pty (fst g') (snd g') in
    wcomp l 1 intch
  end in
  (* Part 1 *)
  let t1 = begin
    let q1 = wcomp gc 1 (wcomp yc 0 (n,nty)) in
    let q2 = wcomp ac 0 g' in
    let q3 = wcomp (wcomp fc 1 (wcomp xc 0 (m,mty))) 0 g' in
    intch_comp_2112 (fst bc) (snd bc) (fst q1) (snd q1) (fst q2) (snd q2) (fst q3) (snd q3)
  end in
  (* Collate *)
  wcomp t0 3 t1

let phase_12 a aty b bty l p =
  let fs,fty = src 0 aty in
  let gs,gty = src 0 bty in
  let c, cty = phase_n0 fs fty gs gty l p in
  phase_of_nat a aty b bty c cty l p phase_01

let phase_22 a aty b bty l p =
  let fs,fty = src 0 aty in
  let gs,gty = src 0 bty in
  let c, cty = phase_n0 fs fty gs gty l p in
  phase_of_nat a aty b bty c cty l p phase_11

let phase_24 m mty n nty l p =
  (* Setup *)
  let a = src 0 mty in
  let b = src 0 nty in
  let ft = tgt 0 (snd a) in
  let gt = tgt 0 (snd b) in
  (* Construct c *)
  let comp = wcomp a 1 b in
  let inner = (Cones.cone_tm (fst comp) l p,Cones.cone_ty (fst comp) (snd comp) l p) in
  let p01 = phase_01 (fst ft) (snd ft) (fst gt) (snd gt) l p in
  let c = wcomp inner 1 p01 in
  (* Produce phase *)
  phase_of_nat m mty n nty (fst c) (snd c) l p phase_12

let phase n i f fty g gty l p =
  let _ = Printf.printf "Constructing phase p^{%d}_{%d} of %s : %s and %s : %s\n%!" n i
    (Unchecked.tm_to_string f)
    (Unchecked.ty_to_string fty)
    (Unchecked.tm_to_string g)
    (Unchecked.ty_to_string gty) in
  match n, i with
  | _, 0 -> phase_n0 f fty g gty l p
  | 0, 1 -> phase_01 f fty g gty l p
  | 1, 1 -> phase_11 f fty g gty l p
  | 1, 2 -> phase_12 f fty g gty l p
  | 2, 1 -> phase_21 f fty g gty l p
  | 2, 2 -> phase_22 f fty g gty l p
  | 2, 4 -> phase_24 f fty g gty l p
  | _, _ -> assert false

let init () =
  Cones.phase := phase
