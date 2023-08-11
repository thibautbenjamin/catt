open Kernel
open Unchecked_types.Unchecked_types(Coh)

(* returns the associator pairing up the middle two cells of a composite of
    (2*k) 1-cells. The argument is the integer k *)
let middle_associator k =
  let tdb i = Var (Db i) in
  let ps = Builtin.ps_comp (2*k) in
  let src = Coh(Builtin.comp_n (2*k), Unchecked.(identity_ps ps)) in
  let tgt =
    let sub_assoc_middle =
      let rec compute_sub i =
        match i with
        | i when i <= 0 -> [Var(Db 0), false]
        | i when i < k ->
            (tdb (2*i), true)::(tdb (2*i-1), false)::(compute_sub (i-1))
        | i when i = k ->
            let sub_comp =
              [ tdb (2*k+2),true;
                tdb (2*k+1), false;
                tdb (2*k), true;
                tdb (2*k-1), false;
                tdb (2*k-3), false]
            in
            let comp = (Coh(Builtin.comp_n 2, sub_comp)) in
            (comp, true)::(tdb (2*k+1), false)::(compute_sub (k-1))
        | i -> (tdb (2*i+2), true)::(tdb (2*i+1), false)::(compute_sub (i-1))
      in
      compute_sub (2*k-1)
    in
    Coh(Builtin.comp_n (2*k-1), sub_assoc_middle)
  in
  Coh.check_inv ps src tgt ("focus", 0, None)
