module Test

eqb : Nat -> Nat -> Bool
eqb  Z     Z    = True
eqb  Z    (S _) = False
eqb (S _)  Z    = False
eqb (S n) (S m) = eqb n m

negb : Bool -> Bool
negb True = False
negb False = True

andb : Bool -> Bool -> Bool
andb True b = b
andb False _ = False

infixr 2 =?
(=?) : Nat -> Nat -> Bool
n =? m = eqb n m

plus_id_example : (n, m : Nat) -> n = m -> n + n = m + m
plus_id_example Z Z Refl = Refl
plus_id_example Z (S _) Refl impossible
plus_id_example (S _) Z Refl impossible
plus_id_example (S j) (S j) Refl = Refl

plus_id_exercise : (n, m, o: Nat) -> n = m -> m = o -> n + m = m + o
plus_id_exercise Z Z Z eq_nm eq_mo = Refl
plus_id_exercise Z Z (S _) _ Refl impossible
plus_id_exercise Z (S _) _ Refl _ impossible
plus_id_exercise (S _) Z _ Refl _ impossible
plus_id_exercise (S _) (S _) Z _ Refl impossible
plus_id_exercise (S j) (S j) (S j) Refl Refl = Refl

mult_0_plus : (n, m : Nat) -> (0 + n) * m = n * m
mult_0_plus Z Z = Refl
mult_0_plus Z (S k) = Refl
mult_0_plus (S k) Z = Refl
mult_0_plus (S k) (S j) = Refl

mult_S_1 : (n, m : Nat) -> m = S n -> m * (1 + n) = m * m
mult_S_1 Z Z Refl impossible
mult_S_1 Z (S Z) Refl = Refl
mult_S_1 (S _) Z Refl impossible
mult_S_1 (S k) (S (S k)) Refl = Refl

plus_1_neq_0 : (n : Nat) -> n + 1 =? 0 = False
plus_1_neq_0 Z = Refl
plus_1_neq_0 (S k) = Refl

negb_involutive : (b : Bool) -> negb (negb b) = b
negb_involutive False = Refl
negb_involutive True = Refl

andb_commutative : (b, c : Bool) -> andb b c = andb c b
andb_commutative False False = Refl
andb_commutative False True = Refl
andb_commutative True False = Refl
andb_commutative True True = Refl

andb3_exchange : (b, c, d : Bool) -> andb (andb b c) d = andb (andb b d) c
andb3_exchange False False False = Refl
andb3_exchange False False True = Refl
andb3_exchange False True False = Refl
andb3_exchange False True True = Refl
andb3_exchange True False False = Refl
andb3_exchange True False True = Refl
andb3_exchange True True False = Refl
andb3_exchange True True True = Refl

andb_true_elim2 : (b, c : Bool) -> andb b c = True -> c = True
andb_true_elim2 False False Refl impossible
andb_true_elim2 False True Refl impossible
andb_true_elim2 True False Refl impossible
andb_true_elim2 True True prf = Refl

zero_nbeq_plus_1 : (n : Nat) -> 0 =? (n + 1) = False
zero_nbeq_plus_1 Z = Refl
zero_nbeq_plus_1 (S k) = Refl
