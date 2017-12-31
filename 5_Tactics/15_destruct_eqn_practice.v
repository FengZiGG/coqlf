Definition id_b (a : bool) := a.
Definition not_b (a : bool) := if a then False else True.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:eq1.
  - (* b = true *) destruct (f true) eqn:eq2.
    + (* f b = true *) rewrite eq2. exact eq2.
    + (* f b = false *) destruct (f false) eqn:eq3.
      * (* f false = true *) exact eq2.
      * (* f false = false *) exact eq3.
  - (* b = false *) destruct (f false) eqn:eq2.
    + (* f b = false *) destruct (f true) eqn:eq3.
      * (* f false = true *) exact eq3.
      * (* f false = false *) exact eq2.
    + (* f b = true *) rewrite eq2. exact eq2.
Qed.