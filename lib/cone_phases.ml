open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

let tdb i = Var(Db i)
let wcomp = Functorialisation.wcomp

let rec bdry n (t,ty) =
  match n, ty with
  | 0, _ -> (t,ty),(t,ty)
  | 1, Arr(b,s,t) -> (s,b),(t,b)
  | _, Arr(b,s,_) -> bdry (n-1) (s,b)
  | _, _ -> assert false

let src n t = fst (bdry n t)
let tgt n t = snd (bdry n t)

let src_cone n t l p = Cones.cone_tmty (src n t) l p

(* Unchecked method to unwrap n(n-1)n composites *)
let unwrap_composite_lr t =
  let (ps,_,_),s = match t with
  | (Coh(c,s),_) -> Coh.forget c,s
  | _ -> assert false in
  let len = List.length s in
  let d = Unchecked.dim_ps ps in
  let left,_ = List.nth s (len-(2*d)-1) in
  let right,_ = List.nth s (len-(2*d+2)-1) in
  let rl,_ = List.nth s (len-(2*d-1)-1) in
  let (ll,b),(rr,_) = bdry 1 t in
  (left,Arr(b,ll,rl)), (right,Arr(b,rl,rr))

(* Super unchecked method to reassociate nested binary composites
   Matches f * (g * h) and constructs sub out of (x(f)y(g)z)
   (f * g) * h -> f * (g * h)
*)
let assoc_right_sub t =
  let (a,aty), inner = unwrap_composite_lr t in
  let s = match inner with
  | (Coh(_,s),_) -> s
  | _ -> assert false in
  (List.hd s)::(List.nth s 1)::(List.nth s 2)::(List.nth s 3)
  ::(a,true)::(Unchecked.ty_to_sub_ps aty)

let reassoc_forward t =
  let d = Unchecked.dim_ty (snd t) in
  let assoc = Suspension.coh (Some(d-1)) (Builtin.assoc) in
  let sub = assoc_right_sub t in
  Unchecked.coh_ty assoc sub

let reassoc_backward t =
  let d = Unchecked.dim_ty (snd t) in
  let assoc = Suspension.coh (Some(d-1)) (Inverse.coh (Builtin.assoc)) in
  let sub = assoc_right_sub t in
  Unchecked.coh_ty assoc sub

let phase_n0 f g l p =
  let d = Unchecked.dim_ty (snd f) in
  let fc = Cones.cone_tmty f l p in
  let gc = Cones.cone_tmty g l p in
  let h = tgt (d-1) g in
  wcomp gc 1 (wcomp fc 0 h)

let phase_01 f g l p =
  let x,_ = src 1 f in
  let (y,_),(z,_) = bdry 1 g in
  let xc = Cones.cone_tm x l p in
  let sub_ps = [fst g,true;z,false;fst f,true;y,false;xc,true;x,false;Var(p),false] in
  Unchecked.coh_ty Builtin.assoc sub_ps

let assoc_conj m =
  (* Part 2 *)
  let part2s,part2t = bdry 1 m in
  (* Part 1 *)
  let part1 = reassoc_forward part2s in
  (* Part 3 *)
  let part3 = reassoc_backward part2t in
  let part3t,_ = tgt 1 part3 in
  (* Collate *)
  let d = Unchecked.dim_ty (snd m) in
  let comp = Suspension.coh (Some(d-1)) (Builtin.comp_n 3) in
  let sub = (fst part3,true)::(part3t,false)::(fst m,true)::(fst part2t,false)::(fst part1,true)::(Unchecked.ty_to_sub_ps (snd part1)) in
  Unchecked.coh_ty comp sub

let nat_of_phase a b l p ph =
  (* Setup *)
  let fs,(ft,_) = bdry 1 a in
  let gs,(gt,_) = bdry 1 b in
  let r, _ = ph fs gs l p in
  let v1,v2 = match fs,gs with
  | (Var(v1),_),(Var(v2),_) -> v1,v2
  | _, _ -> assert false in
  (* Compute nat *)
  let nat = Inverse.compute_inverse (Functorialisation.tm_one_step_tm r [v2;v1]) in
  let nat_sub = [Var.Bridge(v2),fst b;Var.Plus(v2),gt;Bridge(v1),fst a;Plus(v1),ft] in
  match nat with
  | Coh(c,s) -> Unchecked.coh_ty c (Unchecked.sub_ps_apply_sub s nat_sub)
  | _ -> assert false

let phase_of_nat a b c l p ph =
  let d = Unchecked.dim_ty (snd c) in
  let nat = nat_of_phase a b l p ph in
  let middle = wcomp c (d-1) nat in
  assoc_conj middle

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

let intch_comp_2112 (m,mty) n (p,pty) q =
  let p_sub = Unchecked.ty_to_sub_ps pty in
  let sub = (fst q,true)::(fst (tgt 1 q),false)::(p,true)::(List.hd p_sub)::(List.nth p_sub 1)::(List.nth p_sub 2)::(fst n,true)::(fst (tgt 1 n),false)::(m,true)::(Unchecked.ty_to_sub_ps mty) in
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

let intch_comp_21 m n c =
  let sub = (fst c,true)::(fst (tgt 1 c),false)::(fst n,true)::(fst (tgt 1 n),false)::(fst m,true)::(Unchecked.ty_to_sub_ps (snd m)) in
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

let intch_comp_20 m n g =
  let sub = (fst g,true)::(fst (tgt 1 g),false)::(fst n,true)::(fst (tgt 1 n),false)::(fst m,true)::(Unchecked.ty_to_sub_ps (snd m)) in
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

let intch_phase_11 a b c =
  let c_sub = Unchecked.ty_to_sub_ps (snd c) in
  let sub = (fst c,true)::(List.hd c_sub)::(List.nth c_sub 1)::(List.nth c_sub 2)::(fst b,true)::(fst (tgt 1 b),false)::(fst a,true)::(Unchecked.ty_to_sub_ps (snd a)) in
  Unchecked.coh_ty intch_phase_11_coh sub

let phase_11 a b l p =
  (* Setup *)
  let xc = src_cone 2 a l p in
  let fc = src_cone 1 a l p in
  let gc = src_cone 1 b l p in
  let c = wcomp xc 0 a in
  (* Core of the phase *)
  let intch = intch_phase_11 fc c b in
  let middle = wcomp gc 1 intch in
  (* Conjugate by assoc *)
  assoc_conj middle

let phase_21 m n l p =
  let g' = tgt 2 n in
  let xc = src_cone 3 m  l p in
  let yc = src_cone 3 n l p in
  let fc = src_cone 2 m l p in
  let gc = src_cone 2 n l p in
  let ac = src_cone 1 m l p in
  let bc = src_cone 1 n l p in
  (* Part 0 *)
  let t0 = begin
    let l = wcomp bc 2 (wcomp gc 1 (wcomp yc 0 n)) in
    let p = wcomp fc 1 (wcomp xc 0 m) in
    let intch = intch_comp_20 ac p g' in
    wcomp l 1 intch
  end in
  (* Part 1 *)
  let t1 = begin
    let q1 = wcomp gc 1 (wcomp yc 0 n) in
    let q2 = wcomp ac 0 g' in
    let q3 = wcomp (wcomp fc 1 (wcomp xc 0 m)) 0 g' in
    intch_comp_2112 bc q1 q2 q3
  end in
  (* Collate *)
  wcomp t0 3 t1

let phase_12 a b l p =
  let fs = src 1 a in
  let gs = src 1 b in
  let c = phase_n0 fs gs l p in
  phase_of_nat a b c l p (!Cones.phase 0 1)

let phase_22 m n l p =
  let a = src 1 m in
  let b = src 1 n in
  let c = phase_n0 a b l p in
  phase_of_nat m n c l p (!Cones.phase 1 1)

let phase_24 m n l p =
  (* Setup *)
  let a = src 1 m in
  let b = src 1 n in
  let ft = tgt 1 a in
  let gt = tgt 1 b in
  (* Construct c *)
  let p10 = (!Cones.phase 1 0) a b l p in
  let p11 = (!Cones.phase 1 1) a b l p in
  let p01 = (!Cones.phase 0 1) ft gt l p in
  let c = wcomp (wcomp p10 2 p11) 1 p01 in
  (* Produce phase *)
  phase_of_nat m n c l p (!Cones.phase 1 2)

let phase_23 m n l p =
  let a = src 1 m in
  let b = src 1 n in
  let f = src 1 a in
  let g = src 1 b in
  let xc = src_cone 1 f l p in
  let t0 = wcomp (phase_n0 a b l p) 2 ((!Cones.phase 1 1) a b l p) in
  let t1 = wcomp (phase_n0 f g l p) 1 (wcomp (wcomp xc 0 m) 0 n) in
  let t2 = (!Cones.phase 0 1) (tgt 2 m) (tgt 2 n) l p in
  intch_comp_21 t0 t1 t2

let phase n i f g l p =
  let _ = Printf.printf "Constructing phase p^{%d}_{%d} of %s : %s and %s : %s\n%!" n i
    (Unchecked.tm_to_string (fst f))
    (Unchecked.ty_to_string (snd f))
    (Unchecked.tm_to_string (fst g))
    (Unchecked.ty_to_string (snd g)) in
  match n, i with
  | _, 0 -> phase_n0 f g l p
  | 0, 1 -> phase_01 f g l p
  | 1, 1 -> phase_11 f g l p
  | 1, 2 -> phase_12 f g l p
  | 2, 1 -> phase_21 f g l p
  | 2, 2 -> phase_22 f g l p
  | 2, 3 -> phase_23 f g l p
  | 2, 4 -> phase_24 f g l p
  | _, _ -> assert false

(*
  \t{a\s_{0} b} = (\ldots(((\phi^{n}_{1}(\t a, \t b) \s_{k^{(n)}_{1}} \phi
  ^{k^{(n)}_{1}}_{m^{(n)}_{1}+1}(\tgt{k^{(n)}_{1}}(a),\tgt{k^{(n)}_{1}}(b))) \s_{k^{(n)}_{2}} \phi
  ^{k^{(n)}_{2}}_{m^{(n)}_{2}+1}(\tgt{k^{(n)}_{2}}(a),\tgt{k^{(n)}_{2}}(b))) \s_{k^{(n)}_{3}} \phi
  ^{k^{(n)}_{3}}_{m^{(n)}_{3}+1}(\tgt{k^{(n)}_{3}}(a),\tgt{k^{(n)}_{3}}(b)))\ldots) \s_{k^{(n)}_{2^{n}}} \phi
  ^{k^{(n)}_{2^{n}}}_{m^{(n)}_{2^{n}}+1}(\tgt{k^{(n)}_{2^{n}}}(a),\tgt{k^{(n)}_{2^{n}}}(b))
*)
let phase_seq_len n = ((1 lsl (n+1))-1)

let phase_seq n len f g l p =
  let primary = List.init len (Cones.primary_seq n) in
  let secondary = List.init len (Cones.secondary_seq n) in
  let d' = Unchecked.dim_ty (snd f) in
  let ph j k = phase (j-1) k (tgt (d'-j) f) (tgt (d'-j) g) l p in
  List.map2 ph primary secondary

let cone_comp_n0n n f g l p =
  let init = phase n 0 f g l p in
  let list = phase_seq n (phase_seq_len n) f g l p in
  let merge l r = wcomp l ((Unchecked.dim_ty (snd r))-1) r in
  List.fold_left merge init list

let init () =
  Cones.phase := phase;
  Cones.cone_comp_n0n := cone_comp_n0n
