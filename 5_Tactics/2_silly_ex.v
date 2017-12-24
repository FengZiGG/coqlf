Require Import List.
Import ListNotations.

Search (nat -> bool).
Definition evenb := Nat.even.
Definition oddb := Nat.odd.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq1.
  exact eq2.
Qed.

Theorem silly_ex' :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros eq1 eq2.
  rewrite (eq1 3).
  + (* oddb 4 = true, which is goal *) exact eq_refl.
  + (* evenb 3, which is a given *) exact eq2.
Qed.
