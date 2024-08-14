open Kernel
open Unchecked_types.Unchecked_types(Coh)

let rec bdry n ty =
  match ty, n with
  | Arr(b,s,t), 0 -> b,s,t
  | Arr(b,_,_), _ -> bdry (n-1) b
  | _, _ -> assert false

let src n ty = let b,s,_ = bdry n ty in s,b
let tgt n ty = let b,_,t = bdry n ty in t,b

let phase_01 f fty g gty l p =
  let x,_ = src 0 fty in
  let _,y,z = bdry 0 gty in
  let assoc = Builtin.assoc in
  (* This inlines coning of variable to avoid mutual deps *)
  let xc = Cones.cone_tm x l p in
  let sub_ps = [g,true;z,false;f,true;y,false;xc,true;x,false;Var(p),false] in
  Unchecked.coh_ty assoc sub_ps

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
  | _, _ -> assert false

let init () =
  Cones.phase := phase
