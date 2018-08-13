total plus_O_n : (n : Nat) -> n + 0 = n
plus_O_n Z      = Refl
plus_O_n (S n') = let I_H = plus_O_n n' in rewrite I_H in Refl

total plus_n_O : (n : Nat) -> n = n + 0
plus_n_O Z      = Refl
plus_n_O (S n') = let I_H = plus_n_O n' in rewrite I_H in Refl

total minus_diag : (n : Nat) -> minus n n = 0
minus_diag Z      = Refl
minus_diag (S n') = rewrite minus_diag n' in Refl

total mult_0_r : (n : Nat) -> n * 0 = 0
mult_0_r Z      = Refl
mult_0_r (S n') = rewrite mult_0_r n' in Refl

total plus_n_Sm : (n : Nat) -> (m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm Z _      = Refl
plus_n_Sm (S n') m = let I_H = plus_n_Sm n' m in rewrite I_H in Refl

total fancy_lemma : (n : Nat) -> (m : Nat) -> n + S m = S (m + n)
fancy_lemma Z m      = rewrite (plus_n_O m) in Refl
fancy_lemma (S n') m = let I_H = fancy_lemma n' m in
                       let asdf = plus_n_Sm m n' in
                       rewrite sym asdf in rewrite I_H in Refl

total plus_comm : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_comm n Z      = rewrite plus_O_n n in Refl
plus_comm n (S m') = rewrite fancy_lemma n m' in Refl

total plus_assoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc n m Z      = rewrite plus_O_n m in rewrite plus_O_n (n + m) in Refl
plus_assoc n m (S p') = let IH = plus_assoc n m p' in
                        rewrite sym (plus_n_Sm m p') in
                        rewrite fancy_lemma n (plus m p') in
                        rewrite sym (plus_comm n (plus m p')) in
                        rewrite IH in
                        rewrite plus_n_Sm (plus n m) p' in
                        Refl

double : (n : Nat) -> Nat
double Z      = Z
double (S n') = S (S (double n'))

total double_plus : (n : Nat) -> double n = n + n
double_plus Z      = Refl
double_plus (S n') = let IH = double_plus n' in
                     rewrite IH in 
                     rewrite plus_n_Sm n' n' in 
                     Refl

evenb : (n : Nat) -> Bool
evenb (S (S n')) = evenb n'
evenb (S n')     = False
evenb Z          = True

negb : Bool -> Bool
negb True  = False
negb False = True

total negb_involutive : (b : Bool) -> negb (negb b) = b
negb_involutive False = Refl
negb_involutive True  = Refl

evenb_S : (n : Nat) -> evenb (S n) = negb (evenb n)
evenb_S Z = Refl
evenb_S (S n') = rewrite evenb_S n' in rewrite negb_involutive (evenb n') in Refl
