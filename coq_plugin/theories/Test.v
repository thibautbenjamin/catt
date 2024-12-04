From Catt Require Import Loader.

Catt "identity" "composite" "ternarycomposite" "whiskr"  "hcomp" "vcomp"  "exchange" "assoc" "assocI" "assocU" "complex" From File "../../test.t/features/coq_plugin.catt".

Print catt_coh_identity.
Print catt_coh_composite.
Print catt_coh_ternarycomposite.
Print catt_coh_whiskr.

Catt "eh" From File "../../test.t/coverage/eckmann-hilton-optimized.catt".
Print catt_tm_eh.
