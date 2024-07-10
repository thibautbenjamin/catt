From Catt Require Import Loader.

Catt "identity" "composite" "ternarycomposite" "whiskr"  "hcomp" "vcomp"  "exch" "assoc" "assocI" "assocU" "complex" From File "../../test/coq_plugin.catt".

Print catt_identity.
Print catt_composite.
Print catt_ternarycomposite.
Print catt_whiskr.

Catt "eh" From File "../../../syllepsis/eckmann-hilton-minimal.catt".
Print catt_eh.
