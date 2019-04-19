{- NOTES: 
  Use -p pruviloj to load the lib
  The data types for Bool and Nat are reused from the prelude
  and the duplicates of the operators on those types are prefixed with ^
-}

module Basics

import Pruviloj

%default total
%language ElabReflection

data Day 
  = Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

next_weekday : Day -> Day
next_weekday Monday = Tuesday
next_weekday Tuesday = Wednesday
next_weekday Wednesday = Thursday
next_weekday Thursday = Friday
next_weekday _ = Monday

test_next_weekday : next_weekday (next_weekday Saturday) = Tuesday
test_next_weekday = Refl

-- data Bool = True | False

negb : Bool -> Bool
negb True = False
negb False = True

andb : Bool -> Bool -> Bool
andb True b = b
andb False _ = False

orb : Bool -> Bool -> Bool
orb True _ = True
orb False b = b

test_orb1 : orb True False = True
test_orb1 = Refl
test_orb2 : orb False False = False
test_orb2 = Refl
test_orb3 : orb False True = True
test_orb3 = Refl
test_orb4 : orb True True = True
test_orb4 = Refl

infixr 3 ^&&
(^&&) : Bool -> Bool -> Bool
a ^&& b = andb a b

infixr 2 ^||
(^||) : Bool -> Bool -> Bool
a ^|| b = orb a b

nandb : Bool -> Bool -> Bool
nandb a b = negb (andb a b)

test_nandb1 : nandb True False = True
test_nandb1 = Refl
test_nandb2 : nandb False False = True
test_nandb2 = Refl
test_nandb3 : nandb False True = True
test_nandb3 = Refl
test_nandb4 : nandb True True = False
test_nandb4 = Refl

andb3 : Bool -> Bool -> Bool -> Bool
andb3 True b c = andb b c
andb3 False _ _ = False

test_andb31 : andb3 True True True = True
test_andb31 = Refl
test_andb32 : andb3 False True True = False
test_andb32 = Refl
test_andb33 : andb3 True False True = False
test_andb33 = Refl
test_andb34 : andb3 True True False = False
test_andb34 = Refl

data RGB = Red | Green | Blue
data Color = Black | White | Primary RGB

monochrome : Color -> Bool
monochrome Black = True
monochrome White = True
monochrome (Primary _) = False

isred : Color -> Bool
isred Black = False
isred White = False
isred (Primary Red) = True
isred (Primary _) = False

data Bit = B0 | B1
data Nybble = Bits (Bit, Bit, Bit, Bit)

all_zero : Nybble -> Bool
all_zero (Bits (B0, B0, B0, B0)) = True
all_zero _ = False

-- data Nat = O | S Nat

pred : Nat -> Nat 
pred Z = Z
pred (S n) = n

minustwo : Nat -> Nat
minustwo Z = Z
minustwo (S Z) = Z
minustwo (S (S n)) = n

evenb : Nat -> Bool
evenb Z = True
evenb (S Z) = False
evenb (S (S n)) = evenb n

oddb : Nat -> Bool
oddb n = negb (evenb n)

test_oddb1 : oddb 1 = True
test_oddb1 = Refl
test_oddb2 : oddb 4 = False
test_oddb2 = Refl

plus : Nat -> Nat -> Nat
plus Z m = m
plus (S n) m = S (Basics.plus n m)

mult : Nat -> Nat -> Nat
mult Z b = Z
mult (S n) m = Basics.plus m (Basics.mult n m)

test_mult1 : Basics.mult 3 3 = 9
test_mult1 = Refl

minus : Nat -> Nat -> Nat
minus Z b = Z
minus n@(S _) Z = n 
minus (S n) (S m) = Basics.minus n m

exp : (base : Nat) -> (power: Nat) -> Nat
exp base Z = S Z
exp base (S power) = Basics.mult base (Basics.exp base power)

factorial : Nat -> Nat
factorial Z = S Z
factorial n@(S n') = Basics.mult n (Basics.factorial n')

test_factorial1 : Basics.factorial 3 = 6
test_factorial1 = Refl
test_factorial2 : Basics.factorial 5 = Basics.mult 10 12
test_factorial2 = Refl

infixl 6 ^+
(^+) : Nat -> Nat -> Nat
n ^+ m = Basics.plus n m

infixl 6 ^-
(^-) : Nat -> Nat -> Nat
n ^- m = Basics.minus n m

infixl 7 ^*
(^*) : Nat -> Nat -> Nat
n ^* m = Basics.mult n m

eqb : Nat -> Nat -> Bool
eqb  Z     Z    = True
eqb  Z    (S _) = False
eqb (S _)  Z    = False
eqb (S n) (S m) = eqb n m

leb : Nat -> Nat -> Bool
leb Z _= True
leb (S _) Z = False
leb (S n) (S m) = leb n m

test_leb1 : leb 2 2 = True
test_leb1 = Refl
test_leb2 : leb 2 4 = True
test_leb2 = Refl
test_leb3 : leb 4 2 = False
test_leb3 = Refl

ltb : Nat -> Nat -> Bool
ltb n m = andb (leb n m) (negb (eqb n m))

test_ltb1 : ltb 2 2 = False
test_ltb1 = Refl
test_ltb2 : ltb 2 4 = True
test_ltb2 = Refl
test_ltb3 : ltb 4 2 = False
test_ltb3 = Refl

plus_O_n : (n : Nat) -> 0 ^+ n = n
plus_O_n n = Refl

plus_1_1 : (n : Nat) -> 1 ^+ n = S n
plus_1_1 n = Refl

mult_0_1 : (n : Nat) -> Z ^* n = Z
mult_0_1 n = Refl
 
plus_id_example : (n : Nat) -> (m : Nat) -> n = m -> n ^+ n = m ^+ m
plus_id_example = %runElab ( do 
  intro `{{n}}
  intro `{{m}}
  intro `{{n_eq_m}}
  rewriteWith (Var `{{n_eq_m}})
  reflexivity
)

plus_id_exercise : (n : Nat) -> (m : Nat) -> (o : Nat) -> n = m -> m = o -> n ^+ m = m ^+ o
plus_id_exercise = ?rhs
-- This should work:
-- plus_id_exercise = %runElab ( do
--   intro `{{n}}
--   intro `{{m}}
--   intro `{{o}}
--   intro `{{n_eq_m}}
--   intro `{{m_eq_o}}
--   rewriteWith (Var `{{m_eq_o}})
--   rewriteWith (Var `{{n_eq_m}})
--   reflexivity
-- )
-- Same in coq works(intermediate goals look the same)
-- Theorem plus_id_exercise : forall n m o : nat,
--   n = m -> m = o -> n + m = m + o.
-- Proof.
--   intro n.
--   intro m.
--   intro o.
--   intro n_eq_m.
--   intro m_eq_o.
--   rewrite <- m_eq_o.
--   rewrite <- n_eq_m.
--   reflexivity.
-- Qed.