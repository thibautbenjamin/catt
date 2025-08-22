open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let pad p q previous v sigma =
  Construct.comp3 p
    (Construct.tm_app (Functorialisation.tm previous [ (v, 1) ]) sigma)
    q

let hexcomp fminus fplus ybridge fbridge gminus gplus gbridge zbridge hminus
    hplus hbridge =
  let d = Construct.dim fminus - 1 in
  let db n = Var.Db n in
  let hex =
    Functorialisation.coh (Builtin.comp_n 3) [ db 6; db 4; db 3; db 2; db 1 ]
  in
  let hex = Suspension.checked_tm (Some d) hex in
  let x = Construct.src 1 fminus in
  let yminus = Construct.tgt 1 fminus in
  let yplus = Construct.tgt 1 fplus in
  let zminus = Construct.src 1 hminus in
  let zplus = Construct.src 1 hplus in
  let w = Construct.tgt 1 hminus in
  let sub =
    let tm = Construct.to_tm in
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

let repad p_0 p_1 f q_0 q_1 g previous iota_minus iota_plus v sub =
  let padding_0, padding_1 = Tm.bdry previous in
  hexcomp p_0 p_1
    Construct.(apply_sub (tm_app previous iota_minus) sub)
    f
    Construct.(tm_app (Functorialisation.tm padding_0 [ (v, 1) ]) sub)
    Construct.(tm_app (Functorialisation.tm padding_1 [ (v, 1) ]) sub)
    Construct.(inverse (tm_app (Functorialisation.tm previous [ (v, 1) ]) sub))
    Construct.(apply_sub (tm_app previous iota_plus) sub)
    q_0 q_1 g

let repad_old p_0 p_1 f q_0 q_1 g previous iota_minus iota_plus v sub =
  let padding_0 = Construct.src 1 previous in
  let padding_1 = Construct.tgt 1 previous in
  hexcomp p_0 p_1
    Construct.(apply_sub (apply_sub previous iota_minus) sub)
    f
    Construct.(apply_sub (functorialise padding_0 [ v ]) sub)
    Construct.(apply_sub (functorialise padding_1 [ v ]) sub)
    Construct.(inverse (apply_sub (functorialise previous [ v ]) sub))
    Construct.(apply_sub (apply_sub previous iota_plus) sub)
    q_0 q_1 g
