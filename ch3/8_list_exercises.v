Load "7_list_induction.v".

Theorem app_nil_r : forall l : natlist, l ++ [] = l.
Proof.
  intros l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1.
  - (* base *) simpl. rewrite app_nil_r. reflexivity.
  - (* i.h. *) simpl. rewrite -> IHl1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
  intros l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  case l1.
  - (* empty list case *) rewrite app_assoc. reflexivity.
  - (* l1 = n : l1'    *) intros n n0. simpl. rewrite app_assoc. rewrite app_assoc. reflexivity.
Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | [ ]       => []
  | cons 0 l' => (nonzeros l')
  | cons x l' => cons x (nonzeros l')
  end.

Lemma nonzeros_app : forall l1 l2 : natlist, nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHl1. case n. (* we run case on n for cons zero on nonzeros *)
    + (* zero *) reflexivity.
    + (* S _  *) intros n0. simpl. rewrite <- IHl1. simpl. reflexivity.
Qed.
