open Common
module Ps_reduction (Strictness : StrictnessLv)
= struct
  module Kernel = Kernel.Kernel(Strictness)
  module Coh = Kernel.Coh
  module Unchecked = Kernel.Unchecked
  module Builtin = Builtin.Builtin(Strictness)
  open Kernel.Unchecked_types

  let tdb i = Var (Var.Db i)

  let rec reduce i ps =
    match i,ps with
    | _, Br [] -> Br []
    | 0, _ -> Br [Br []]
    | i, Br l -> Br (List.map (reduce (i-1)) l)

  let reduction_sub ps =
    let rec aux i ps =
      match i,ps with
      | _, Br[] -> [tdb 0, true]
      | 0, Br l ->
        let k = List.length l in
        [Coh(Builtin.comp_n k,(Unchecked.(identity_ps (Br l)))), true ;
         tdb (2*k-1), false;
         tdb 0, true]
      | i, Br l -> Unchecked.suspwedge_subs_ps (List.map (aux (i-1)) l) l
    in
    aux (Unchecked.dim_ps ps - 1) ps

  let coh c =
    let ps,ty,name = Coh.forget c in
    let name = Unchecked.full_name name in
    let ps = reduce (Unchecked.dim_ps ps - 1) ps in
    if Coh.is_inv c then
      let src,tgt =
        match ty with
        | Arr (_,src,tgt) -> src,tgt
        | _ -> Error.fatal "type of a coherence must be an arrow type"
      in
      Coh.check_inv ps src tgt (name^"_red", 0, None)
    else
      let src,tgt = Coh.noninv_srctgt c in
      Coh.check_noninv ps src tgt (name^"_red", 0, None)
end
