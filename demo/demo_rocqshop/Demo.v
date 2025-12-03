From Catt Require Import Loader.

Catt "trans" "whisk" From File "demo1.catt".

Print catt_coh_trans.
Print catt_coh_whisk.

Catt "eh" From File "demo2.catt".
Print catt_tm_eh.
Eval cbv in catt_tm_eh.
