Load "4_bag_functions".


Fixpoint count' (v:nat) (s:bag) : nat :=
  match s with
  | []        => 0
  | cons x s' => match (Nat.eqb x v) with
                | true  => 1 + (count' x s') (* this is the only difference with original count. *)
(* The reason for this change is when we case on Nat.eqb n v in the theorem below, it's using different tricks to prove *)
                | false => count' v s'
                end
  end.


Example cool_example_1 : count' 1 (sum [ 1 ; 2 ; 3 ] [ 1; 2; 3 ] ) = 2 * count' 1 [ 1 ; 2 ; 3 ].
Proof.
  simpl.
  reflexivity.
Qed.

Require Import PeanoNat.

Lemma really_fancy : forall (s : bag) (v : nat), S (count' v s) = count' v (cons v s).
Proof.
  intros s v.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

SearchAbout ((_ =? _) = true).
Check Nat.eqb_eq.
Axiom woot : forall (v n : nat), Nat.eqb v n = true <-> v = n.

Lemma some_lemma : forall (s1 s2 : bag) (v n : nat), Nat.eqb n v = true -> S (count' n s1) + count' v s2 = S (count' v s1 + count' v s2).
Proof.
  intros s1 s2 v n.
  intros n_eqb_v.
  assert (n = v).
  rewrite <- Nat.eqb_eq.
  exact n_eqb_v.
  rewrite H.
  reflexivity.
Qed.

Theorem my_cool_theorem : forall (s1 s2 : bag) (v : nat), count' v s1 + count' v s2 = count' v (sum s1 s2).
Proof.
  intros s1 s2 v.
  induction s1.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) case (Nat.eqb n v) eqn:Hn.
    + (* v == n *)
      (* Nat.eqb is boolean, let's first convert it to = *)
      assert (n = v). rewrite <- Nat.eqb_eq. exact Hn.
      (* At this point we have H : n = v. Just rewrite *)
      simpl. rewrite Hn.
      (* Use our fancy lemma just for demo purposes, we can just rewrite H instead *)
      rewrite (some_lemma s1 s2 v n Hn). rewrite IHs1. rewrite H. reflexivity.
    + (* v != n *) simpl. rewrite Hn. exact IHs1.
Qed.

Theorem my_cool_theorem_simpl : forall (s1 s2 : bag) (v : nat), count v s1 + count v s2 = count v (sum s1 s2).
Proof.
  intros s1 s2 v.
  induction s1.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) case (Nat.eqb n v) eqn:Hn.
    + (* v == n *) simpl. rewrite Hn. simpl. rewrite IHs1. reflexivity.
    + (* v != n *) simpl. rewrite Hn. exact IHs1.
Qed.
