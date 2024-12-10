open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

type display_map = (Var.t * Var.t) list

let rec pullback c1 sub c2 dm =
  match (c2, dm) with
  | [], [] -> (c1, [])
  | (x, (_, expl)) :: ctx, (p, y) :: dm when x = y ->
      let ctx, names = pullback c1 sub ctx dm in
      (ctx, (x, (Unchecked.tm_apply_sub (Var p) sub, expl)) :: names)
  | (x, (ty, expl)) :: ctx, (_ as dm) ->
      let ctx, names = pullback c1 sub ctx dm in
      let newvar = Var.fresh () in
      let ty = Unchecked.ty_apply_sub ty names in
      ((newvar, (ty, expl)) :: ctx, (x, (Var newvar, expl)) :: names)
  | [], _ :: _ -> assert false
