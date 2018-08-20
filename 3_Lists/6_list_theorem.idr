import MyLists

total
even : (n : Nat) -> Bool
even (S (S n')) = even n'
even (S n')     = False
even Z          = True

total even_members : Natlist -> Natlist
even_members Nil         = Nil
even_members (Cons x l') = if (even x) then (Cons x (even_members l')) else even_members l'
-- Alternate definition:
--even_members (Cons x l') with (even x)
--  even_members (Cons x l') | True  = Cons x (even_members l')
--  even_members (Cons x l') | False = (even_members l')

total has_odd : Natlist -> Bool
has_odd Nil         = False
has_odd (Cons x l') with (even x)
  has_odd (Cons x l') | True  = has_odd l'
  has_odd (Cons x l') | False = True

-- This is a unit test
asdf : has_odd (even_members (Cons 1 (Cons 2 (Cons 3 Nil)))) = False
asdf = Refl

postulate woot : (n : Nat) -> even n = True

-- This is a proof (doesn't check a specific value, but checks for all possible values
even_members_list_only_even : (l : Natlist) -> has_odd (even_members l) = False
even_members_list_only_even Nil = Refl
even_members_list_only_even (Cons n l') with (even n) proof a
  even_members_list_only_even (Cons n l') | True  = let IH = even_members_list_only_even l' in rewrite sym a in IH
  even_members_list_only_even (Cons n l') | False = let IH = even_members_list_only_even l' in IH
