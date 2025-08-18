open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let pad p q previous v sigma =
  Construct.comp3 p
    (Construct.apply_sub (Construct.functorialise previous [ v ]) sigma)
    q

let hexcomp fminus fplus ybridge fbridge gminus gplus gbridge zbridge hminus
    hplus hbridge =
  let d = Construct.dim fminus - 1 in
  let hex = Functorialisation.coh_all (Builtin.comp_n 3) in
  let hex = Suspension.checked_tm (Some d) hex in
  let x = Construct.src 1 fminus in
  let yminus = Construct.tgt 1 fminus in
  let yplus = Construct.tgt 1 fplus in
  let zminus = Construct.src 1 hminus in
  let zplus = Construct.src 1 hplus in
  let w = Construct.tgt 1 hminus in
  let tm = Construct.to_tm in
  let sub =
    (tm hbridge, true)
    :: (tm hplus, false)
    :: (tm hminus, false)
    :: (tm w, false)
    :: (tm gbridge, true)
    :: (tm gplus, false)
    :: (tm gminus, false)
    :: (tm zbridge, false)
    :: (tm zplus, false)
    :: (tm zminus, false)
    :: (tm fbridge, true)
    :: (tm fplus, false)
    :: (tm fminus, false)
    :: (tm ybridge, false)
    :: (tm yplus, false)
    :: (tm yminus, false)
    :: (tm x, false)
    :: Unchecked.ty_to_sub_ps (Construct.to_ty w)
  in
  (* The call to sub_ps_to_sub is a bit of a hack, relying on the fact that all
     checked terms use deBruijn. Further refactoring to be done in the kernel to
     enforce this more statically *)
  Construct.tm_app hex (Unchecked.sub_ps_to_sub sub)

let repad p_0 p_1 f_n q_0 q_1 g_n previous_repadding iota_minus iota_plus v_i
    sigma =
  let padding_0 = Construct.src 1 previous_repadding in
  let padding_1 = Construct.tgt 1 previous_repadding in
  hexcomp p_0 p_1
    (Construct.apply_sub
       (Construct.apply_sub previous_repadding iota_minus)
       sigma)
    f_n
    (Construct.apply_sub (Construct.functorialise padding_0 [ v_i ]) sigma)
    (Construct.apply_sub (Construct.functorialise padding_1 [ v_i ]) sigma)
    (Construct.inverse
       (Construct.apply_sub
          (Construct.functorialise previous_repadding [ v_i ])
          sigma))
    (Construct.apply_sub
       (Construct.apply_sub previous_repadding iota_plus)
       sigma)
    q_0 q_1 g_n
