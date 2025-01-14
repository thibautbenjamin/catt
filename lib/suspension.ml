open Kernel

let rec iter_n_times n f base =
  if n <= 0 then base else f (iter_n_times (n - 1) f base)

let iter_option f n base =
  match n with None -> base | Some n -> iter_n_times n f base

let pp_data = iter_option Unchecked.suspend_pp_data
let ps = iter_option Unchecked.suspend_ps
let ty = iter_option Unchecked.suspend_ty
let tm = iter_option Unchecked.suspend_tm
let sub_ps = iter_option Unchecked.suspend_sub_ps
let ctx = iter_option Unchecked.suspend_ctx
let sub = iter_option Unchecked.suspend_sub

let coh i coh =
  match i with
  | None | Some 0 -> coh
  | Some _ ->
      let p, t, ppd = Coh.forget coh in
      check_coh (ps i p) (ty i t) (pp_data i ppd)

let checked_tm i t =
  match i with
  | None | Some 0 -> t
  | Some _ -> fst (Tm.apply (ctx i) (tm i) (pp_data i) t)
