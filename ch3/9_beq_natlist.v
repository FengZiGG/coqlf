Load MyLists.

Require Import PeanoNat.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | []       => match l2 with
          | [] => true
          | _  => false
          end
  | cons x l1' => match l2 with
          | []         => false
          | cons y l2' => match (Nat.eqb x y) with
                          | true  => beq_natlist l1' l2'
                          | false => false
                          end
          end
  end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof.
  simpl.
  reflexivity.
Qed.

(*
Axiom woot : forall n, Nat.eqb n n = true.
Search (Nat.eqb _ _). (* We find Nat.eqb_refl *)
*)

Theorem beq_natlist_refl : forall l:natlist, true = beq_natlist l l.
Proof.
  intros l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. (* use simpl to rewrite from definition of beq_natlist *)
               rewrite Nat.eqb_refl. exact IHl.
Qed.
