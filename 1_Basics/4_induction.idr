-- No recursion needed for induction as simple as this in Idris

beq_nat : Nat -> Nat -> Bool
beq_nat Z Z           = True
beq_nat Z (S m')      = False
beq_nat (S n') Z      = False
beq_nat (S n') (S m') = beq_nat n' m'

plus_1_neq_0_firsttry : (n : Nat) -> beq_nat (n + 1) 0 = False
plus_1_neq_0_firsttry Z      = Refl
plus_1_neq_0_firsttry (S n') = Refl

not_b : Bool -> Bool
not_b True  = False
not_b False = True

negb : Bool -> Bool
negb = not_b

negb_involutive : (b : Bool) -> negb (negb b) = b
negb_involutive True  = Refl
negb_involutive False = Refl 

andb : Bool -> Bool -> Bool
andb a b = a && b

andb_commutative : (b : Bool) -> (c : Bool) -> andb b c = andb c b
andb_commutative False False = Refl
andb_commutative False True  = Refl
andb_commutative True False  = Refl
andb_commutative True True   = Refl
