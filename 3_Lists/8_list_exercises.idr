import MyLists

app_nil_r : (l : Natlist) -> app l Nil = l
app_nil_r Nil         = Refl
app_nil_r (Cons x l') = let IH = app_nil_r l' in rewrite IH in Refl

rev_app_distr : (l1, l2 : Natlist) -> rev (app l1 l2) = app (rev l2) (rev l1)
rev_app_distr Nil l2          = let a = app_nil_r (rev l2) in rewrite a in Refl
rev_app_distr (Cons x l1') l2 = let IH = rev_app_distr l1' l2 in
                                let assoc = app_assoc (rev l2) (rev l1') (Cons x Nil) in
                                rewrite IH in rewrite assoc in Refl

rev_involutive : (l : Natlist) -> rev (rev l) = l
rev_involutive Nil = Refl
rev_involutive (Cons x l') = let IH = rev_involutive l' in
                             let distr = rev_app_distr (rev l') (Cons x Nil) in
                             rewrite distr in
                             rewrite IH in Refl

app_assoc4 : (l1, l2, l3, l4 : Natlist) -> app l1 (app l2 (app l3 l4)) = app (app (app l1 l2) l3) l4
app_assoc4 Nil l2 l3 l4          = let assoc = app_assoc l2 l3 l4 in rewrite assoc in Refl
app_assoc4 (Cons x l1') l2 l3 l4 = let assoc  = app_assoc l1' l2 l3 in 
                                   let assoca = sym (app_assoc l1' l2 (app l3 l4)) in
                                   let assocb = app_assoc l1' (app l2 l3) l4 in
                                   rewrite assoc in rewrite assoca in rewrite assocb in (believe_me 1)

nonzeros : Natlist -> Natlist
nonzeros Nil = Nil
nonzeros (Cons Z l) = nonzeros l
nonzeros (Cons x l) = Cons x (nonzeros l)

nonzeros_app : (l1, l2 : Natlist) -> nonzeros (app l1 l2) = app (nonzeros l1) (nonzeros l2)
nonzeros_app Nil l2          = Refl
nonzeros_app (Cons Z l1') l2 = let IH = nonzeros_app l1' l2 in rewrite IH in Refl
nonzeros_app (Cons x l1') l2 = let IH = nonzeros_app (Cons x l1') l2 in rewrite IH in Refl
