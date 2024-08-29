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

(*
  (a *_n b) *_0 (c *_n d) -> (a *_0 c) *_n (b *_0 d)
*)
let intch_comp_n0n_coh n =
  let rec ty n j k = match n with
  | 1 -> Arr(Obj,tdb j,tdb ((2*n-1)+k))
  | _ -> Arr(ty (n-1) j k,tdb ((2*n-2)+k),tdb ((2*n-1)+k)) in
  let fty = ty n 0 0 in
  let gty = ty n 1 (2*n+4) in
  let a = tdb (2*n+2),Arr(fty,tdb (2*n),tdb (2*n+1)) in
  let b = tdb (2*n+4),Arr(fty,tdb (2*n+1),tdb (2*n+3)) in
  let c = tdb (4*n+6),Arr(gty,tdb (4*n+4),tdb (4*n+5)) in
  let d = tdb (4*n+8),Arr(gty,tdb (4*n+5),tdb (4*n+7)) in
  let s,_ = wcomp (wcomp a n b) 0 (wcomp c n d) in
  let t,_ = wcomp (wcomp a 0 c) n (wcomp b 0 d) in
  let inner_ps = Suspension.ps (Some(n-1)) (Br[Br[];Br[]]) in
  let ps = Br[inner_ps;inner_ps] in
  Coh.check_inv ps s t (Printf.sprintf "comp_%d_0_%d_intch" n n,0,[])

let intch_comp_n1n_coh n = Suspension.coh (Some(1)) (intch_comp_n0n_coh (n-1))

let intch_comp_n1n (a,aty) b (c,cty) d =
  let n = Unchecked.dim_ty aty in
  let rec aux s = match s with
  | [] | _::_::_::[] -> []
  | h::tl -> h::(aux tl) in
  let c_sub = aux (Unchecked.ty_to_sub_ps cty) in
  let sub = ((fst d,true)::(fst (tgt 1 d),false)::(c,true)::c_sub) @ ((fst b,true)::(fst (tgt 1 b),false)::(a,true)::(Unchecked.ty_to_sub_ps aty)) in
  Unchecked.coh_ty (intch_comp_n1n_coh (n-1)) sub

(*
  (a *_n b) *_0 g -> (a *_0 g) *_n (b *_0 g)
  https://q.uiver.app/#q=WzAsMyxbMCwwLCIwIl0sWzIsMCwiMSJdLFs0LDAsIjciXSxbMCwxLCIyIiwwLHsiY3VydmUiOi01fV0sWzAsMSwiNSIsMix7ImN1cnZlIjo1fV0sWzAsMSwiMyIsMV0sWzEsMiwiOCIsMV0sWzMsNSwiNCIsMix7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbNSw0LCI2IiwyLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==
*)
let intch_comp_n0_coh n =
  let rec ty n = match n with
  | 0 -> Obj
  | _ -> Arr(ty (n-1),tdb (2*n-2),tdb (2*n-1)) in
  let fty = ty n in
  let a = tdb (2*n+2),Arr(fty,tdb (2*n),tdb (2*n+1)) in
  let b = tdb (2*n+4),Arr(fty,tdb (2*n+1),tdb (2*n+3)) in
  let g = tdb (2*n+6),Arr(Obj,tdb 1,tdb (2*n+5)) in
  let s,_ = wcomp (wcomp a n b) 0 g in
  let t,_ = wcomp (wcomp a 0 g) n (wcomp b 0 g) in
  let ps = Br[Br[];(Suspension.ps (Some(n-1)) (Br[Br[];Br[]]))] in
  Coh.check_inv ps s t (Printf.sprintf "comp_%d_0_intch" n,0,[])

(*
  For n>m
  (a *_n b) *_m c -> (a *_m c) *_n (b *_m c)
*)
let intch_comp_nm_coh n m = Suspension.coh (Some(m-1)) (intch_comp_n0_coh (n-m))

let intch_comp_nm a b c =
  let n = Unchecked.dim_ty (snd a) in
  let m = Unchecked.dim_ty (snd c) in
  let sub_left = (fst b,true)::(fst (tgt 1 b),false)::(fst a,true)::(Unchecked.ty_to_sub_ps (snd a)) in
  let sub_right = (fst c,true)::(Common.take (m) (Unchecked.ty_to_sub_ps (snd c))) in
  Unchecked.coh_ty (intch_comp_nm_coh n m) (sub_right @ sub_left)

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

let phase_n1 m n l p =
  let d = Unchecked.dim_ty (snd m) in
  let g' = tgt (d-1) n in
  let ac,lc = unwrap_composite_lr (tgt 1 (src_cone 0 m l p)) in
  let bc,rc = unwrap_composite_lr (tgt 1 (src_cone 0 n l p)) in
  let t0 = wcomp (wcomp bc (d-1) rc) 1 (intch_comp_nm ac lc g') in
  let t1 = intch_comp_n1n bc rc (wcomp ac 0 g') (wcomp lc 0 g') in
  wcomp t0 d t1

let phase_23 m n l p =
  let a = src 1 m in
  let b = src 1 n in
  let f = src 1 a in
  let g = src 1 b in
  let xc = src_cone 1 f l p in
  let t0 = wcomp ((!Cones.phase 1 0) a b l p) 2 ((!Cones.phase 1 1) a b l p) in
  let t1 = wcomp ((!Cones.phase 0 0) f g l p) 1 (wcomp (wcomp xc 0 m) 0 n) in
  let t2 = (!Cones.phase 0 1) (tgt 2 m) (tgt 2 n) l p in
  intch_comp_nm t0 t1 t2

(*
  \t{a\s_{0} b} = (\ldots(((\phi^{n}_{1}(\t a, \t b) \s_{k^{(n)}_{1}} \phi
  ^{k^{(n)}_{1}}_{m^{(n)}_{1}+1}(\tgt{k^{(n)}_{1}}(a),\tgt{k^{(n)}_{1}}(b))) \s_{k^{(n)}_{2}} \phi
  ^{k^{(n)}_{2}}_{m^{(n)}_{2}+1}(\tgt{k^{(n)}_{2}}(a),\tgt{k^{(n)}_{2}}(b))) \s_{k^{(n)}_{3}} \phi
  ^{k^{(n)}_{3}}_{m^{(n)}_{3}+1}(\tgt{k^{(n)}_{3}}(a),\tgt{k^{(n)}_{3}}(b)))\ldots) \s_{k^{(n)}_{2^{n}}} \phi
  ^{k^{(n)}_{2^{n}}}_{m^{(n)}_{2^{n}}+1}(\tgt{k^{(n)}_{2^{n}}}(a),\tgt{k^{(n)}_{2^{n}}}(b))
*)
let phase_seq_len n = min 4 ((1 lsl (n+1))-1)

let rec phase_of_nat n i a b l p =
  let nat = nat_of_phase a b l p (phase (n-1) (i/2)) in
  let left = phase_merge (n-1) (i/2-1) (src 1 a) (src 1 b) l p in
  assoc_conj (wcomp left (n) nat)

and phase n i f g l p =
  let _ = Printf.printf "Constructing phase p^{%d}_{%d} of %s : %s and %s : %s\n%!" n i
    (Unchecked.tm_to_string (fst f))
    (Unchecked.ty_to_string (snd f))
    (Unchecked.tm_to_string (fst g))
    (Unchecked.ty_to_string (snd g)) in
  match n, i, i mod 2 with
  | _,0,_ -> phase_n0 f g l p
  | 0,1,_ -> phase_01 f g l p
  | 1,1,_ -> phase_11 f g l p
  | _,1,_ -> phase_n1 f g l p
  | 2,3,_ -> phase_23 f g l p
  | _,_,0 -> phase_of_nat n i f g l p
  | _,_,_ -> assert false

and phase_seq n len f g l p =
  let primary = List.init len (Cones.primary_seq n) in
  let secondary = List.init len (Cones.secondary_seq n) in
  let d' = Unchecked.dim_ty (snd f) in
  let ph j k = phase (j-1) k (tgt (d'-j) f) (tgt (d'-j) g) l p in
  List.map2 ph primary secondary

and phase_merge n len f g l p =
  let init = phase n 0 f g l p in
  let list = phase_seq n len f g l p in
  let merge l r = wcomp l ((Unchecked.dim_ty (snd r))-1) r in
  List.fold_left merge init list

let cone_comp_n0n n f g l p = phase_merge n (phase_seq_len n) f g l p

let init () =
  Cones.phase := phase;
  Cones.cone_comp_n0n := cone_comp_n0n
