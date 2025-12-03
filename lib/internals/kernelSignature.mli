open Common

module type S = sig
  exception InvalidPS

  val theory : theory

  module rec Coh :
    (Signature.CohS
      with type innertm = Tm.t
       and type checked_ps = PS.t
       and type checked_tm = Tm.t
       and type checked_ty = Ty.t)

  and Ty :
    (Signature.TyS
      with type checked_tm = Tm.t
       and type checked_coh = Coh.t
       and type checked_sub = Sub.t
       and type checked_ctx = Ctx.t)

  and Tm :
    (Signature.TmS
      with type checked_coh = Coh.t
       and type checked_sub = Sub.t
       and type checked_ty = Ty.t
       and type checked_ctx = Ctx.t)

  and PS :
    (Signature.PSS with type inner_ctx = Ctx.t and type checked_sub = Sub.t)

  and Ctx :
    (Signature.CtxS
      with type checked_ty = Ty.t
       and type checked_coh = Coh.t
       and type checked_tm = Tm.t
       and type checked_ps = PS.t)

  and Sub :
    (Signature.SubS
      with type checked_tm = Tm.t
       and type checked_coh = Coh.t
       and type checked_ctx = Ctx.t)

  type ty = (Coh.t, Tm.t) pty
  type tm = (Coh.t, Tm.t) ptm
  type sub = (Coh.t, Tm.t) psub
  type sub_ps = (Coh.t, Tm.t) psub_ps
  type ctx = (Coh.t, Tm.t) pctx
  type constr = (Coh.t, Tm.t) pconstr
  type meta_ctx = (int * ty) list
  type value = (Coh.t, Tm.t) pvalue
  type decls = (value * string) list
end
