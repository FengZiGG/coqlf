import MyLists

test_rev1 : rev (Cons 1 (Cons 2 (Cons 3 Nil))) = (Cons 3 (Cons 2 (Cons 1 Nil)))
test_rev1 = Refl

test_rev2 : rev Nil = Nil
test_rev2 = Refl

my_fancy_lemma : (l1, l2 : Natlist) -> length (app l1 l2) = length l1 + length l2
my_fancy_lemma Nil l2          = Refl
my_fancy_lemma (Cons x l1') l2 = let IH = my_fancy_lemma l1' l2 in rewrite IH in Refl

testlemma : (n : Nat) -> n + 1 = S n
testlemma Z = Refl
testlemma (S n) = let IH = testlemma n in rewrite IH in Refl

postulate plus_comm : (m, n : Nat) -> m + n = n + m

app_comm : (m, n : Natlist) -> app m n = app n m
app_comm Nil (Cons x l2)         = let IH = app_comm Nil l2 in rewrite IH in Refl
app_comm (Cons x l1) (Cons y l2) = let IH_1 = app_comm l1 (Cons y l2) in
                                   let IH_2 = sym (app_comm (Cons x l1) l2) in
                                   let IH_3 = app_comm l1 l2 in
--rewrite IH_1 in
--rewrite sym IH_2 in
--rewrite IH_3 in
believe_me 1

rev_length_mytry : (l : Natlist) -> length (rev l) = length l
rev_length_mytry Nil         = Refl
rev_length_mytry (Cons x l') = let IH = rev_length_mytry l' in
                               let a  = app_comm (rev l') (Cons x Nil) in
                               rewrite a in
                               rewrite IH in Refl
