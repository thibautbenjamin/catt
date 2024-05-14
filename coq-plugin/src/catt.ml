
let c_Q env sigma =
  let gr = Coqlib.lib_ref "core.eq.type" in
  Evd.fresh_global env sigma gr

let c_R env sigma =
  let gr = Coqlib.lib_ref "core.eq.refl" in
  Evd.fresh_global env sigma gr


let example () =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c_Q = c_Q env sigma in
  let sigma, c_R = c_R env sigma in
  Feedback.msg_notice (Printer.pr_econstr_env env sigma c_R)
