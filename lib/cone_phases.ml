open Kernel
open Unchecked_types.Unchecked_types(Coh)

let phase_01 f fty g gty l p =
  let v,y,z = match fty,gty with
  | Arr(_,Var(v),_),Arr(_,y,z) -> v,y,z
  | _,_ -> assert false in
  let assoc = Builtin.assoc in
  (* This inlines coning of variable to avoid mutual deps *)
  let sub_ps = [g,true;z,false;f,true;y,false;Var(List.assoc v l),true;Var(v),false;Var(p),false] in
  Unchecked.coh_ty assoc sub_ps

let phase_n0 f fty g gty l p =
  let d = Unchecked.dim_ty fty in
  let fc = Cones.cone_tm f l p in
  let fcty = Cones.cone_ty f fty l p in
  let gc = Cones.cone_tm g l p in
  let gcty = Cones.cone_ty g gty l p in
  let inner = Functorialisation.whisk (d-1) 1 0 in
  let inner_sub_ps = Functorialisation.whisk_sub_ps 0 fc fcty g gty in
  let inner, inner_ty = Unchecked.coh_ty inner inner_sub_ps in 
  let outer = Functorialisation.whisk d 0 0 in
  let outer_sub_ps = Functorialisation.whisk_sub_ps 0 gc gcty inner inner_ty in
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
