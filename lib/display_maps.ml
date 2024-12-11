open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

type display_map = (Var.t * Var.t) list

let rec pullback c1 sub c2 dm =
  match (c2, dm) with
  | [], [] -> (c1, [])
  | (x, (_, expl)) :: ctx, (p, (Var y, _)) :: dm when x = y ->
      let ctx, names = pullback c1 sub ctx dm in
      (ctx, (x, (Unchecked.tm_apply_sub (Var p) sub, expl)) :: names)
  | (x, (ty, expl)) :: ctx, (_ as dm) ->
      let ctx, names = pullback c1 sub ctx dm in
      let newvar = Var.fresh () in
      let ty = Unchecked.ty_apply_sub ty names in
      ((newvar, (ty, expl)) :: ctx, (x, (Var newvar, expl)) :: names)
  | [], _ :: _ ->
      Error.fatal
        "wrong data for pullback: display map cannot be longer than the context"

let rec glue s1 s2 right_incl c2 dm =
  match (s2, c2, dm) with
  | [], [], [] -> s1
  | (z, _) :: s2, (x, _) :: c2, (_, (Var y, _)) :: dm when x = y && x = z ->
      let s = glue s1 s2 right_incl c2 dm in
      s
  | (z, (t, e)) :: s2, (x, _) :: c2, (_ as dm) when x = z ->
      let s = glue s1 s2 right_incl c2 dm in
      let var =
        match Unchecked.tm_apply_sub (Var x) right_incl with
        | Var x -> x
        | _ -> assert false
      in
      (var, (t, e)) :: s
  | _, [], _ :: _ ->
      Error.fatal
        "wrong data for pullback gluing: display map cannot be longer than the \
         context"
  | _, _, _ ->
      Error.fatal
        "wrong data pullback gluing: substitution must be point to the context"
