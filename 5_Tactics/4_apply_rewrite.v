(* Briefly explain the difference between the tactics apply and rewrite
What are the situations where both can usefully be applied?

1. We can use apply instead of rewrite where the goal to be proved is exactly
the same as some hypothesis
2. The apply tactic can also be used on hypotheses with implication.
Each of the premises will be treated as subgoals. But for rewrite,
we have to do intros first to put them in hypothesis.
3. We can use apply with previously defined lemmas (same as rewrite)

*)