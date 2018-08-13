plus_id_example : (n : Nat) -> (m : Nat) -> n = m -> n + n = m + m
plus_id_example n m n_eq_m = rewrite n_eq_m in Refl

plus_id_exercise : (n : Nat) -> (m : Nat) -> (o : Nat) -> n = m -> m = o -> n + m = m + o
plus_id_exercise n m o n_eq_m m_eq_o = rewrite n_eq_m in rewrite m_eq_o in Refl

plus_O_n : (n : Nat) -> 0 + n = n
plus_O_n n = Refl

mult_0_plus : (n : Nat) -> (m : Nat) -> (0 + n) * m = n * m
mult_0_plus n m = Refl -- Idris already evaluated 0 + n = n for us

mult_S_1 : (n : Nat) -> (m : Nat) -> m = S n -> m * (1 + n) = m * m
mult_S_1 n m m_eq_S_n = rewrite m_eq_S_n in Refl
