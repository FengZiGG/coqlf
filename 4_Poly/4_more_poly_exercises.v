Load "3_poly_exercises.v".

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Theorem rev_app_distr: forall X (l1 l2 : list X), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros x l1 l2.
  induction l1.
  - (* base *) simpl. rewrite app_nil_r. reflexivity.
  - (* i.h. *) simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X, rev (rev l) = l.
Proof.
  intros x l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.