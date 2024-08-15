open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

let rec bdry n ty =
  match ty, n with
  | Arr(b,s,t), 0 -> b,s,t
  | Arr(b,_,_), _ -> bdry (n-1) b
  | _, _ -> assert false

let src n ty = let b,s,_ = bdry n ty in s,b
let tgt n ty = let b,_,t = bdry n ty in t,b

let whisk n j k f fty g gty =
  let whisk = Functorialisation.whisk n j k in
  let whisk_sub_ps = Functorialisation.whisk_sub_ps k f fty g gty in
  Unchecked.coh_ty whisk whisk_sub_ps

let cone_tmty f fty l p =
  let fcty = Cones.cone_ty f fty l p in
  let fc = Cones.cone_tm f l p in
  fc, fcty

let src_cone n ty l p =
  let s, b = src n ty in
  cone_tmty s b l p

let phase_01 f fty g gty l p =
  let x,_ = src 0 fty in
  let _,y,z = bdry 0 gty in
  let xc = Cones.cone_tm x l p in
  let sub_ps = [g,true;z,false;f,true;y,false;xc,true;x,false;Var(p),false] in
  Unchecked.coh_ty Builtin.assoc sub_ps

(*
https://q.uiver.app/#q=WzAsMyxbMCwwLCIwIl0sWzIsMCwiMSJdLFs0LDAsIjYiXSxbMCwxLCIzIiwxXSxbMCwxLCI1IiwyLHsiY3VydmUiOjR9XSxbMSwyLCI3IiwwLHsiY3VydmUiOi0yfV0sWzEsMiwiOCIsMix7ImN1cnZlIjoyfV0sWzAsMSwiMiIsMCx7ImN1cnZlIjotNH1dLFszLDQsIjYiLDAseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzUsNiwiOSIsMCx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbNywzLCI0IiwwLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==
*)
let intch_11 a aty b bty c cty =
  let tdb i = Var(Db i) in
  let ps = Br[Br[Br[]];Br[Br[];Br[]]] in
  let ifty = Arr(Obj,tdb 0,tdb 1) in
  let igty = Arr(Obj,tdb 1,tdb 7) in
  let iaty = Arr(ifty,tdb 2,tdb 3) in
  let ibty = Arr(ifty,tdb 3,tdb 5) in
  let icty = Arr(igty,tdb 8,tdb 9) in
  let s,_ =
  begin
    let left = Functorialisation.whisk 0 0 1 in
    let left_sub = Functorialisation.whisk_sub_ps 1 (tdb 2) ifty (tdb 10) icty in
    let l, lty = Unchecked.coh_ty left left_sub in
    let inner = Functorialisation.whisk 1 0 0 in
    let inner_sub = Functorialisation.whisk_sub_ps 0 (tdb 4) iaty (tdb 6) ibty in
    let i, ity = Unchecked.coh_ty inner inner_sub in
    let right = Functorialisation.whisk 0 1 0 in
    let right_sub = Functorialisation.whisk_sub_ps 0 i ity (tdb 9) igty in
    let r, rty = Unchecked.coh_ty right right_sub in
    let src = Functorialisation.whisk 1 0 0 in
    let src_sub = Functorialisation.whisk_sub_ps 0 l lty r rty in
    Unchecked.coh_ty src src_sub
  end in
  let t,_ =
  begin
    let left = Functorialisation.whisk 0 1 0 in
    let left_sub = Functorialisation.whisk_sub_ps 0 (tdb 4) iaty (tdb 8) igty in
    let l, lty = Unchecked.coh_ty left left_sub in
    let right = Functorialisation.whisk 0 1 1 in
    let right_sub = Functorialisation.whisk_sub_ps 1 (tdb 6) ibty (tdb 10) icty in
    let r, rty = Unchecked.coh_ty right right_sub in
    let tgt = Functorialisation.whisk 1 0 0 in
    let tgt_sub = Functorialisation.whisk_sub_ps 0 l lty r rty in
    Unchecked.coh_ty tgt tgt_sub
  end in
  let intch = Coh.check_inv ps s t ("phase_11_intch",0,[]) in
  let c_sub = Unchecked.ty_to_sub_ps cty in
  let sub = (c,true)::(List.hd c_sub)::(List.nth c_sub 1)::(List.nth c_sub 2)::(b,true)::(fst (tgt 0 bty),false)::(a,true)::(Unchecked.ty_to_sub_ps aty) in
  Unchecked.coh_ty intch sub

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

let phase_11 a aty b bty l p =
  let xc, xcty = src_cone 1 aty l p in
  let fc, fcty = src_cone 0 aty l p in
  let gc, gcty = src_cone 0 bty l p in
  let c, cty = whisk 0 0 1 xc xcty a aty in
  (* Part 2 *)
  let intch, intchty = intch_11 fc fcty c cty b bty in
  let part2, part2ty = whisk 1 0 1 gc gcty intch intchty in
  let part2b,part2s,part2t = bdry 0 part2ty in
  (* Part 1 *)
  let part1, part1ty = reassoc_forward part2s part2b in
  (* Part 3 *)
  let part3, part3ty = reassoc_backward part2t part2b in
  let part3t,_ = tgt 0 part3ty in
  (* Collate *)
  let comp = Suspension.coh (Some(2)) (Builtin.comp_n 3) in
  let sub = (part3,true)::(part3t,false)::(part2,true)::(part2t,false)::(part1,true)::(Unchecked.ty_to_sub_ps part1ty) in
  Unchecked.coh_ty comp sub

let phase_n0 f fty g gty l p =
  let d = Unchecked.dim_ty fty in
  let fc = Cones.cone_tm f l p in
  let fcty = Cones.cone_ty f fty l p in
  let gc = Cones.cone_tm g l p in
  let gcty = Cones.cone_ty g gty l p in
  let h, hty = if d<2 then g, gty else tgt (d-2) gty in
  let inner = Functorialisation.whisk 0 d 0 in
  let inner_sub_ps = Functorialisation.whisk_sub_ps 0 fc fcty h hty in
  let inner, inner_ty = Unchecked.coh_ty inner inner_sub_ps in 
  let outer = Functorialisation.whisk 1 (d-1) (d-1) in
  let outer_sub_ps = Functorialisation.whisk_sub_ps (d-1) gc gcty inner inner_ty in
  Unchecked.coh_ty outer outer_sub_ps

let phase n i f fty g gty l p =
  let _ = Printf.printf "Constructing phase %d/%d of %s : %s and %s : %s\n%!" n i
    (Unchecked.tm_to_string f)
    (Unchecked.ty_to_string fty)
    (Unchecked.tm_to_string g)
    (Unchecked.ty_to_string gty) in
  match n, i with
  | _, 0 -> phase_n0 f fty g gty l p
  | 0, 1 -> phase_01 f fty g gty l p
  | 1, 1 -> phase_11 f fty g gty l p
  | _, _ -> assert false

let init () =
  Cones.phase := phase