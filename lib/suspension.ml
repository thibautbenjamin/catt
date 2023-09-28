open Kernel
open Kernel.Unchecked_types

let rec iter_n_times n f base =
  if n <= 0 then base else f (iter_n_times (n-1) f base)

let iter_option f n base =
  match n with
  | None -> base
  | Some n -> iter_n_times n f base

let ps = iter_option Unchecked.suspend_ps
let ty = iter_option Unchecked.suspend_ty
let tm = iter_option Unchecked.suspend_tm
let sub_ps = iter_option Unchecked.suspend_sub_ps
let ctx = iter_option Unchecked.suspend_ctx
let coh i coh =
  match i with
  | None -> Cohchecked coh
  | Some 0 -> Cohchecked coh
  | Some _ ->
    let p,t,_ = Coh.forget coh in
    let p = ps i p in
    let t = ty i t in
    Cohdecl(p,t, "dummy")       (* TODO *)
