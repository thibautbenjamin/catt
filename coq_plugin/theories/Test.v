From Catt Require Import Loader.

(* Definition composition (A : Type) (x : A) (y : A) (f : x = y) (z : A) (g : y = z) : x = z := *)
(*   match g in _ = a return x = a with *)
(*   | eq_refl => *)
(*       match f in _ = a return x = a with *)
(*       | eq_refl => eq_refl *)
(*       end *)
(*   end. *)

Definition composition (A : Type) (x : A) (y : A) (f : x = y) (z : A) (g : y = z) : y = z :=
  match g in _ = a return y = a with
  | eq_refl => eq_refl
  end.


Set Printing All.
Print composition.

Catt "ternarycomposite" From File "../../test/coq_plugin.catt".
Print catt_ternarycomposite.


(* Catt "disc" "fst_var" From File "../../test/coq_plugin.catt". *)
(* Print catt_disc. *)
(* Print catt_fst_var. *)
