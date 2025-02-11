From HoTT Require Import Basics.
From HoTT Require Import PathGroupoids.

Section EH.
  Context {A} {x : A}.
  Let c {y} (p : x = y) : p @ 1 = p := match p with 1 => 1 end.
  Let d {y} (p : x = y) : 1 @ p = p := match p with 1 => 1 end.
  Let a {p q : x = x} (h : p = 1) (k : 1 = q) : h @ k = (c p)^ @ (h @@ k) @ d q
      := ltac:(by destruct k; revert p h; rapply paths_ind_r).
  Let b {p q : x = x} (h : p = 1) (k : 1 = q) : h @ k = (d p)^ @ (k @@ h) @ c q
      := ltac:(by destruct k; revert p h; rapply paths_ind_r).
  Let eh (h k : 1 = 1 :> (x = x)) : h @ k = k @ h := a h k @ (b k h)^.

  Set Printing All.
  Set Printing Depth 9999999.
  Eval cbv in eh.
End EH.
