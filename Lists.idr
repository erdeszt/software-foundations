module Lists

import Basics
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

-- WIP at: Exercise: 3 stars, standard, recommended (bag_functions)
