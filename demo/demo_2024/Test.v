Fixpoint N : Type :=
| O : N
| S : forall n : N, N.
