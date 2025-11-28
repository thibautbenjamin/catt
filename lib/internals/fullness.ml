open Std

module Make (K : KernelSignature.S) = struct
  open K

  type res = Inv | NonInv of Tm.t * Tm.t | No

  let rec tm_free_vars tm =
    let fvty = ty_free_vars (Tm.checked_ty tm) in
    match Tm.expr tm with
    | Var x -> x :: fvty
    | Coh (_, sub) | App (_, sub) -> sub_free_vars sub

  and ty_free_vars ty =
    match Ty.expr ty with
    | Obj -> []
    | Arr (t, u, v) ->
        List.unions [ ty_free_vars t; tm_free_vars u; tm_free_vars v ]

  and sub_free_vars s = List.concat (List.map tm_free_vars s.list)

  let ty_contains_all_vars t =
    List.included (Ctx.domain (Ty.ctx t)) (ty_free_vars t)

  let tm_contains_all_vars t =
    List.included (Ctx.domain (Ty.ctx (Tm.checked_ty t))) (tm_free_vars t)

  let is_inv_dim t =
    match Theory.theory.invertibility with
    | None -> false
    | Some d when d >= Ty.dim t -> false
    | _ -> true

  let check_full_inv t =
    if is_inv_dim t || ty_contains_all_vars t then Inv else No

  let check_full_noninv ps t =
    match Ty.expr t with
    | Obj -> No
    | Arr (_, src, tgt) -> (
        try
          let src_inclusion = PS.source ps in
          let src = Tm.preimage src src_inclusion in
          if not (tm_contains_all_vars src) then No
          else
            let tgt_inclusion = PS.target ps in
            let tgt = Tm.preimage tgt tgt_inclusion in
            if not (tm_contains_all_vars tgt) then No else NonInv (src, tgt)
        with NotInImage -> No)

  let check ps t =
    match check_full_inv t with
    | Inv -> Inv
    | NonInv _ -> assert false
    | No -> check_full_noninv ps t
end
