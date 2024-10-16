open Kernel
open Unchecked_types.Unchecked_types (Coh)(Tm)

let meta_namer_ty = ref 0
let meta_namer_tm = ref 0

let new_ty () =
  let meta = !meta_namer_ty in
  meta_namer_ty := !meta_namer_ty + 1;
  Meta_ty meta

let new_tm () =
  let i = !meta_namer_tm in
  let meta = i in
  meta_namer_tm := !meta_namer_tm + 1;
  (Meta_tm meta, (i, new_ty ()))
