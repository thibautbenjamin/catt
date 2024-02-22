open Kernel
open Unchecked_types.Unchecked_types(Coh)

let coh_transformation coh ~compute_ps_ty ~compute_name =
  let ps,ty,pp_data = Coh.forget coh in
  let ctx = Unchecked.ps_to_ctx ps in
  let new_ctx,ty = compute_ps_ty ps ty in
  let ps = Kernel.PS.(forget (mk (Kernel.Ctx.check new_ctx))) in
  let _, names,_ = Unchecked.db_levels new_ctx in
  let ty = Unchecked.rename_ty ty names in
  let pp_data = compute_name ctx pp_data in
  check_coh ps ty pp_data
