From Catt Require Import Loader.

Catt "identity" "composite" "ternarycomposite" "whiskr"  "hcomp" "vcomp"  "exch" "assoc" "assocI" "assocU" "complex" From File "../../test.t/features/coq_plugin.catt".

Print catt_identity.
Print catt_composite.
Print catt_ternarycomposite.
Print catt_whiskr.

Catt "eh" From File "../../test.t/coverage/eckmann-hilton-optimized.catt".
Print catt_eh.
