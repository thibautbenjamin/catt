open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let rec ctx n =
  match n with
  | n when n <= 0 -> Unchecked.ps_to_ctx (Br [])
  | 1 -> Unchecked.ps_to_ctx (Br [ Br [] ])
  | n -> Functorialisation.ctx (ctx (n - 1)) [ base (n - 1); filler (n - 1) ]

and base n =
  match n with
  | n when n <= 0 -> assert false
  | 1 -> Var.Db 0
  | n -> Var.Bridge (base (n - 1))

and filler n =
  match n with
  | n when n <= 0 -> Var.Db 0
  | 1 -> Var.Db 2
  | n -> Var.Bridge (filler (n - 1))

(* Composition of two cones *)
let ctx_c, right_incl =
  Display_maps.pullback (ctx 2)
    [
      (Var.Db 2, (Var (Var.Plus (Var.Db 2)), false));
      (Var.Db 1, (Var (Var.Db 1), false));
      (Var.Db 0, (Var (Var.Plus (Var.Db 0)), false));
    ]
    (ctx 2)
    [ (Var.Db 2, Var.Db 2); (Var.Db 1, Var.Db 1); (Var.Db 0, Var.Db 0) ]
