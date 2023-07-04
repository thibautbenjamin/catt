open Common




  match tm with
  match ty with

let ctx = Translate_raw.ctx

let ty c ty =
  let ty = Syntax.remove_let_ty ty in
  let c = Kernel.Ctx.check c in
  Translate_raw.ty c ty

let tm c tm =
  let tm = Syntax.remove_let_tm tm in
  let c = Kernel.Ctx.check c in
  Translate_raw.tm c tm

let ty_in_ps ps t =
  let t = Syntax.remove_let_ty t in
  let ps = Translate_raw.ctx ps in
  let src = Kernel.Ctx.check ps in
  let t = Translate_raw.ty src t in
  let _, names,_ = Unchecked.db_levels ps in
  Unchecked.rename_ty t names

let ps p =
  let p = Translate_raw.ctx p in
  Kernel.PS.(forget (mk (Kernel.Ctx.check p)))
