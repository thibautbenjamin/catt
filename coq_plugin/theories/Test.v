From Catt Require Import Loader.

Definition composition (A : Type) (x : A) (y : A) (f : x = y) (z : A) (g : y = z) : x = z :=
  match g in _ = a return x = a with
  | eq_refl =>
      match f in _ = a return x = a with
      | eq_refl => eq_refl
      end
  end.

(* Definition whiskering (A:Type) (x : A) (y : A) (f : x = y) (g : x = y) (a : f = g) (z : A) (h : y = z) : *)
(*   composition A x y f z h = composition A x y g z h *)
(*   := *)
(*   match h with *)
(*   | eq_refl => *)
(*       match a with *)
(*       | eq_refl => eq_refl *)
(*       end *)
(*   end. *)

Set Printing All.
Print composition.
(* Print whiskering. *)

Catt "identity"  "composite" "ternarycomposite" "whisk" From File "../../test/coq_plugin.catt".
Print catt_identity.
(* Print catt_composite. *)
(* Print catt_ternarycomposite. *)


(* Catt "disc" "fst_var" From File "../../test/coq_plugin.catt". *)

(* Print catt_disc. *)
(* Print catt_fst_var. *)
