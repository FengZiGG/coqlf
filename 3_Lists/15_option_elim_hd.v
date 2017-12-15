Load "14_hd_error.v".

Theorem option_elim_hd : forall (l:natlist) (default:nat), hd' default l = option_elim default (hd_error l).
Proof.
  intros l default.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. reflexivity.
Qed.