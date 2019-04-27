module Lists

import Basics
import Induction
import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection

NatProd : Type
NatProd = (Nat, Nat)

swap_pair : (p : NatProd) -> NatProd
swap_pair (a, b) = (b, a)

surjective_pairing : (n, m : Nat) -> (n, m) = (fst (n, m), snd (n, m))
surjective_pairing n m = Refl
-- or with Elab
-- surjective_pairing = %runElab (do { intros; reflexivity })

surjective_pairing' : (p : NatProd) -> p = (fst p, snd p)
surjective_pairing' (a, b) = Refl

snd_fst_is_swap : (p: NatProd) -> (snd p, fst p) = swap_pair p
snd_fst_is_swap (a, b) = Refl

fst_swap_is_snd : (p: NatProd) -> fst (swap_pair p) = snd p
fst_swap_is_snd (a, b) = Refl

NatList : Type
NatList = List Nat

repeat : (n, count : Nat) -> NatList
repeat n Z = [n]
repeat n (S k) = n :: repeat n k

length' : NatList -> Nat
length' [] = Z
length' (_ :: xs) = S (length xs)

app : NatList -> NatList -> NatList
app [] ys = ys
app (x :: xs) ys = x :: (app xs ys)

test_app1 : [1, 2, 3] `app` [4, 5] = [1, 2, 3, 4, 5]
test_app1 = Refl
test_app1' : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]
test_app1' = Refl
test_app2 : [] `app` [1, 2, 3] = [1, 2, 3]
test_app2 = Refl
test_app3 : [1, 2, 3] `app` [] = [1, 2, 3]
test_app3 = Refl

hd : (default : Nat) -> NatList -> Nat
hd default [] = default
hd _ (x :: _) = x

tl : NatList -> NatList
tl [] = []
tl (_ :: xs) = xs

test_hd1 : hd 0 [1, 2, 3] = 1
test_hd1 = Refl
test_hd2 : hd 0 [] = 0
test_hd2 = Refl
test_tl : tl [1, 2, 3] = [2, 3]
test_tl = Refl

nonzeros : NatList -> NatList
nonzeros [] = []
nonzeros (Z :: xs) = nonzeros xs
nonzeros (x :: xs) = x :: nonzeros xs

test_nonzeros : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3]
test_nonzeros = Refl

oddmembers : NatList -> NatList
oddmembers [] = []
oddmembers (x :: xs) = if oddb x then x :: oddmembers xs else oddmembers xs

test_oddmembers : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3]
test_oddmembers = Refl

countoddmembers : NatList -> Nat
countoddmembers xs = length (oddmembers xs)

test_countoddmembers1 : countoddmembers [1, 0, 3, 1, 4, 5] = 4
test_countoddmembers1 = Refl
test_countoddmembers2 : countoddmembers [0, 2, 4] = 0
test_countoddmembers2 = Refl
test_countoddmembers3 : countoddmembers [] = 0
test_countoddmembers3 = Refl

alternate : NatList -> NatList -> NatList
alternate ixs iys = go True ixs iys where
  go : (fromFirst: Bool) -> NatList -> NatList -> NatList
  go _     []        ys        = ys
  go _     xs        []        = xs
  go True  (x :: xs) ys        = x :: go False xs ys
  go False xs        (y :: ys) = y :: go True xs ys

test_alternate1 : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6]
test_alternate1 = Refl
test_alternate2 : alternate [1] [4, 5, 6] = [1, 4, 5, 6]
test_alternate2 = Refl
test_alternate3 : alternate [1, 2, 3] [4] = [1, 4, 2, 3]
test_alternate3 = Refl
test_alternate4 : alternate [] [20, 30] = [20, 30]
test_alternate4 = Refl

Bag : Type
Bag = NatList

count : Nat -> Bag -> Nat
count _ [] = 0
count v (x :: xs) = if v == x then S (count v xs) else count v xs

test_count1 : count 1 [1, 2, 3, 1, 4, 1] = 3
test_count1 = Refl
test_count2 : count 6 [1, 2, 3, 1, 4, 1] = 0
test_count2 = Refl

sum : Bag -> Bag -> Bag
sum xs ys = xs ++ ys

test_sum1 : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3
test_sum1 = Refl

add : Nat -> Bag -> Bag
add v xs = v :: xs

test_add1 : count 1 (add 1 [1, 4, 1]) = 3
test_add1 = Refl
test_add2 : count 5 (add 1 [1, 4, 1]) = 0
test_add2 = Refl

member : Nat -> Bag -> Bool
member _ [] = False
member v (x :: xs) = v == x || member v xs

test_member1 : member 1 [1, 4, 1] = True
test_member1 = Refl
test_member2 : member 2 [1, 4, 1] = False
test_member2 = Refl

remove_one : Nat -> Bag -> Bag
remove_one _ [] = []
remove_one v (x :: xs) = if v == x then xs else x :: remove_one v xs

test_remove_one1 : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0
test_remove_one1 = Refl
test_remove_one2 : count 5 (remove_one 5 [2, 1, 4, 1]) = 0
test_remove_one2 = Refl
test_remove_one3 : count 4 (remove_one 5 [2, 1, 4, 5, 1, 4]) = 2
test_remove_one3 = Refl
test_remove_one4 : count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 1
test_remove_one4 = Refl

remove_all : Nat -> Bag -> Bag
remove_all _ [] = []
remove_all v (x :: xs) = if v == x then remove_all v xs else x :: remove_all v xs

test_remove_all1 : count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0
test_remove_all1 = Refl
test_remove_all2 : count 5 (remove_all 5 [2, 1, 4, 1]) = 0
test_remove_all2 = Refl
test_remove_all3 : count 4 (remove_all 5 [2, 1, 4, 5, 1, 4]) = 2
test_remove_all3 = Refl
test_remove_all4 : count 5 (remove_all 5 [2, 1, 5, 4, 5, 1, 4, 5, 1, 4]) = 0
test_remove_all4 = Refl

subset : Bag -> Bag -> Bool
subset [] _ = True
subset (s :: ss) xs =
  if member s xs
    then subset ss (remove_one s xs)
    else False

test_subset1 : subset [1, 2] [2, 1, 4, 1] = True
test_subset1 = Refl
test_subset2 : subset [1, 2, 2] [2, 1, 4, 1] = False
test_subset2 = Refl

nil_app : (l : NatList) -> [] ++ l = l
nil_app l = Refl

tl_length_pred : (l : NatList) -> pred (length l) = length (tl l)
tl_length_pred [] = Refl
tl_length_pred (x :: xs) = Refl

-- With Elab
-- tl_length_pred = %runElab ( do
--   intro `{{l}}
--   induction (Var `{{l}})
--   compute
--   reflexivity
--   attack
--   intro `{{n}}
--   intro `{{xs}}
--   intro `{{ih}}
--   compute
--   reflexivity
--   solve
-- )

app_assoc : (l1, l2, l3 : NatList) -> (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
app_assoc [] l2 l3 = Refl
app_assoc (x :: xs) l2 l3 =
 let rec = app_assoc xs l2 l3 in
 rewrite rec in Refl

-- app_assoc = %runElab ( do
--   intro `{{l1}}
--   intro `{{l2}}
--   intro `{{l3}}
--   induction (Var `{{l1}})
--   compute
--   reflexivity
--   attack
--   intro `{{n}}
--   intro `{{xs}}
--   intro `{{ih}}
--   compute
--   rewriteWith (Var `{{ih}})
--   reflexivity
--   solve
-- )

rev : NatList -> NatList
rev [] = []
rev (x :: xs) = rev xs ++ [x]

test_rev1 : rev [1, 2, 3] = [3, 2, 1]
test_rev1 = Refl
test_rev2 : rev [] = []
test_rev2 = Refl

app_length : (l1, l2 : NatList) -> length (l1 ++ l2) = length l1 + length l2
app_length [] l2 = Refl
app_length (x :: xs) l2 =
  let rec = app_length xs l2 in
  rewrite rec in
  Refl

rev_length : (l : NatList) -> length (rev l) = length l
rev_length [] = Refl
rev_length (x :: xs) =
  let rec = rev_length xs in
  rewrite sym rec in
  rewrite app_length (rev xs) [x] in
  rewrite plus_1_1 (length (rev xs))  in
  Refl

app_nil_r : (l : NatList) -> l ++ [] = l
app_nil_r [] = Refl
app_nil_r (x :: xs) =
  let rec = app_nil_r xs in
  rewrite rec in
  Refl

-- app_nil_r = %runElab ( do
--   intro `{{l}}
--   induction (Var `{{l}})
--   compute
--   reflexivity
--   attack
--   intro `{{n}}
--   intro `{{xs}}
--   intro `{{ih}}
--   compute
--   rewriteWith (Var `{{ih}})
--   reflexivity
--   solve
-- )

rev_app_distr : (l1, l2 : NatList) -> rev (l1 ++ l2) = rev l2 ++ rev l1
rev_app_distr [] l2 = rewrite app_nil_r (rev l2) in Refl
rev_app_distr (x :: xs) l2 =
  let rec = rev_app_distr xs l2 in
  rewrite rec in
  rewrite app_assoc (rev l2) (rev xs) [x] in
  Refl

rev_involutive : (l : NatList) -> rev (rev l) = l
rev_involutive [] = Refl
rev_involutive (x :: xs) =
  let rec = rev_involutive xs in
  rewrite rev_app_distr (rev xs) [x] in
  rewrite rec in
  Refl

app_assoc4 : (l1, l2, l3, l4 : NatList) -> l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4
app_assoc4 [] [] l3 l4 = Refl
app_assoc4 [] (x :: xs) l3 l4 = rewrite app_assoc xs l3 l4 in Refl
app_assoc4 (x :: xs) l2 l3 l4 =
  let rec = app_assoc4 xs l2 l3 l4 in
  rewrite rec in
  Refl

nonzeros_app : (l1, l2 : NatList) -> nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
nonzeros_app [] l2 = Refl
nonzeros_app (Z :: xs) l2 =
  let rec = nonzeros_app xs l2 in
  rewrite rec in
  Refl
nonzeros_app ((S k) :: xs) l2 =
  let rec = nonzeros_app xs l2 in
  rewrite rec in
  Refl

eqblist : (l1, l2 : List Nat) -> Bool
eqblist [] [] = True
eqblist [] l2 = False
eqblist (x :: xs) [] = False
eqblist (x :: xs) (y :: ys) = x == y && eqblist xs ys

test_eqblist1 : eqblist [] [] = True
test_eqblist1 = Refl
test_eqblist2 : eqblist [1, 2, 3] [1, 2, 3] = True
test_eqblist2 = Refl
test_eqblist3 : eqblist [1, 2, 3] [1, 2, 4] = False
test_eqblist3 = Refl

eq_refl_True : (a, b : Nat) -> Maybe (a == b = True)
eq_refl_True Z Z = Just Refl
eq_refl_True Z (S k) = Nothing
eq_refl_True (S k) Z = Nothing
eq_refl_True (S k) (S j) = eq_refl_True k j

eq_refl_True' : (a : Nat) -> ((a == a) = True)
eq_refl_True' Z = Refl
eq_refl_True' (S k) = eq_refl_True' k

eqblist_refl : (l : List Nat) -> True = eqblist l l
eqblist_refl [] = Refl
eqblist_refl (Z :: xs) =
  let rec = eqblist_refl xs in
  rewrite rec in
  Refl
eqblist_refl ((S k) :: xs) =
  rewrite eq_refl_True' k in
  let rec = eqblist_refl xs in
  rewrite rec in
  Refl
-- eqblist_refl = %runElab ( do
--   intro `{{l}}
--   induction (Var `{{l}})
--   compute
--   reflexivity
--   attack
--   intro `{{n}}
--   intro `{{ns}}
--   intro `{{ih}}
--   compute
--   rewriteWith (Var `{{ih}})
--   induction (Var `{{n}})
--   compute
--   reflexivity
--   attack
--   intro `{{nn}}
--   intro `{{ihh}}
--   compute
--   rewriteWith (Var `{{ihh}})
--   reflexivity
--   solve
--   solve
-- )


