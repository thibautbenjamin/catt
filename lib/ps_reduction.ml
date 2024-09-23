open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh)

let tdb i = Var (Var.Db i)

let rec reduce i ps =
  match (i, ps) with
  | _, Br [] -> Br []
  | 0, _ -> Br [ Br [] ]
  | i, Br l -> Br (List.map (reduce (i - 1)) l)

let reduction_sub ps =
  let rec aux i ps =
    match (i, ps) with
    | _, Br [] -> [ (tdb 0, true) ]
    | 0, Br [ Br [] ] -> [ (tdb 2, true); (tdb 1, false); (tdb 0, false) ]
    | 0, Br l ->
        let k = List.length l in
        [
          (Coh (Builtin.comp_n k, Unchecked.(identity_ps (Br l))), true);
          (tdb ((2 * k) - 1), false);
          (tdb 0, false);
        ]
    | i, Br l -> Unchecked.suspwedge_subs_ps (List.map (aux (i - 1)) l) l
  in
  aux (Unchecked.dim_ps ps - 1) ps

let coh c =
  let ps, _, name = Coh.forget c in
  let name = Unchecked.full_name name in
  let ps = reduce (Unchecked.dim_ps ps - 1) ps in
  if Coh.is_inv c then Error.fatal "cannot reduce invertible coherences"
  else
    let src, tgt, _ = Coh.noninv_srctgt c in
    Coh.check_noninv ps src tgt (name ^ "_red", 0, [])
