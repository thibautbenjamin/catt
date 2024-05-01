open Kernel

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
  | None | Some 0 -> coh
  | Some n ->
    let p,t,(name,susp,f) = Coh.forget coh in
    let f = match f with
    | None -> f
    | Some(l) ->
        let pad = List.init (2*n) (fun _ -> 0) in
        Some(List.concat [l;pad])
    in check_coh (ps i p) (ty i t) (name,susp+n,f)
