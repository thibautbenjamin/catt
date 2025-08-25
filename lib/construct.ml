open Common
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

(* returns the n-composite of a (n+j)-cell with a (n+k)-cell *)
let whisk3 n j k l =
  let comp = Builtin.comp_n 3 in
  let func_data = [ (Var.Db 6, l); (Var.Db 4, k); (Var.Db 2, j) ] in
  let whisk = Functorialisation.coh_successively comp func_data in
  Suspension.checked_tm (Some n) whisk

let whisk3_sub_ps k t1 ty1 t2 ty2 l t3 ty3 =
  let rec take n l =
    match l with h :: t when n > 0 -> h :: take (n - 1) t | _ -> []
  in
  let sub_base = Unchecked.ty_to_sub_ps ty1 in
  let sub_ext1 = take ((2 * k) + 1) (Unchecked.ty_to_sub_ps ty2) in
  let sub_ext2 = take ((2 * l) + 1) (Unchecked.ty_to_sub_ps ty3) in
  List.concat
    [
      [ (t3, true) ];
      sub_ext2;
      [ (t2, true) ];
      sub_ext1;
      [ (t1, true) ];
      sub_base;
    ]

let wcomp3 (f, fty) n (g, gty) m (h, hty) =
  let j = Unchecked.dim_ty fty - n - 1 in
  let k = Unchecked.dim_ty gty - n - 1 in
  let l = Unchecked.dim_ty hty - m - 1 in
  let whisk = whisk3 n j k l in
  let whisk_sub_ps = whisk3_sub_ps k f fty g gty l h hty in
  let whisk_sub = Unchecked.sub_ps_to_sub whisk_sub_ps in
  (App (whisk, whisk_sub), Unchecked.ty_apply_sub_ps (Tm.ty whisk) whisk_sub_ps)

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

let intch_comp_mn a b c =
  let m = Unchecked.dim_ty (snd a) in
  let n = Unchecked.dim_ty (snd b) in
  let sub_left = (fst a, true) :: Unchecked.ty_to_sub_ps (snd a) in
  let sub_right =
    (fst c, true)
    :: (fst (tgt 1 c), false)
    :: (fst b, true)
    :: Common.take ((2 * n) - (2 * m) + 1) (Unchecked.ty_to_sub_ps (snd b))
  in
  let coh = Builtin.intch_comp_nm_coh n m in
  let coh = Opposite.coh coh [ 1 ] in
  let sub = sub_right @ sub_left in
  let _, ty, _ = Coh.forget coh in
  (Coh (coh, sub), Unchecked.ty_apply_sub_ps ty sub)

let opposite (t, ty) op_data = (Opposite.tm t op_data, Opposite.ty ty op_data)
let inv (t, ty) = (Inverse.compute_inverse t, Inverse.ty ty)
