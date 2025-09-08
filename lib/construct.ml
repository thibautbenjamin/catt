open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

type constr = tm * ty

let rec bdry n (t, ty) =
  match (n, ty) with
  | 0, _ -> ((t, ty), (t, ty))
  | 1, Arr (b, s, t) -> ((s, b), (t, b))
  | _, Arr (b, s, _) -> bdry (n - 1) (s, b)
  | _, _ -> assert false

let _src n t = fst (bdry n t)
let tgt n t = snd (bdry n t)
let wcomp = Functorialisation.wcomp
let () = Builtin.wcomp := wcomp

let intch_comp_nm a b c =
  let n = Unchecked.dim_ty (snd a) in
  let m = Unchecked.dim_ty (snd c) in
  let sub_left =
    (fst b, true)
    :: (fst (tgt 1 b), false)
    :: (fst a, true)
    :: Unchecked.ty_to_sub_ps (snd a)
  in
  let sub_right =
    (fst c, true) :: Common.take m (Unchecked.ty_to_sub_ps (snd c))
  in
  let coh = Builtin.intch_comp_nm_coh n m in
  let sub = sub_right @ sub_left in
  let _, ty, _ = Coh.forget coh in
  (Coh (coh, sub), Unchecked.ty_apply_sub_ps ty sub)

let inv (t, ty) = (Inverse.compute_inverse t, Inverse.ty ty)
