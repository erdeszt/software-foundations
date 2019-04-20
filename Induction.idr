module Induction

import Basics
import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection

partial
proofByInductionOnNat' : Elab () -> Elab ()
proofByInductionOnNat' introRest = do
  intro `{{n}}
  introRest
  induction (Var `{{n}})
  compute
  reflexivity
  attack
  intro `{{nn}}
  intro `{{ih}}
  compute
  rewriteWith (Var `{{ih}})
  reflexivity
  solve

partial
proofByInductionOnNat : Elab ()
proofByInductionOnNat = proofByInductionOnNat' (pure ())

plus_n_0 : (n : Nat) -> n = n + 0
plus_n_0 = %runElab proofByInductionOnNat

minus_diag : (n : Nat) -> minus n n = 0
minus_diag = %runElab proofByInductionOnNat

mult_0_r : (n : Nat) -> n * 0 = 0
mult_0_r = %runElab proofByInductionOnNat

plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm = %runElab (proofByInductionOnNat' (intro `{{m}}))

plus_1_1 : (n : Nat) -> plus n 1 = S n
plus_1_1 Z = Refl
plus_1_1 (S k) =
  let rec = plus_1_1 k in
  rewrite rec in Refl

plus_comm : (n, m : Nat) -> n + m = m + n
plus_comm Z n = plus_comm_Z
  where
    plus_comm_Z : m = plus m 0
    plus_comm_Z {m = Z} = Refl
    plus_comm_Z {m = (S k)} =
      let rec = plus_comm_Z {m = k} in
      rewrite rec in Refl
plus_comm (S k) m = rewrite plus_comm k m in plus_comm_S k m
  where
    plus_comm_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
    plus_comm_S k Z = Refl
    plus_comm_S k (S m) = rewrite plus_comm_S k m in Refl

plus_assoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc = %runElab (proofByInductionOnNat' (do { intro `{{m}}; intro `{{p}} }))

double : Nat -> Nat
double Z = Z
double (S n) = S (S (double n))

double_plus : (n : Nat) -> double n = n + n
double_plus Z = Refl
double_plus (S k) = double_lemma k
  where
    double_lemma : (k : Nat) -> S (S (double k)) = S (plus k (S k))
    double_lemma Z = Refl
    double_lemma (S k) =
      let rec = double_lemma k in
      rewrite rec in
      rewrite plus_comm k (S k) in
      rewrite plus_comm k (S (S k)) in
      Refl

evenb_S : (n : Nat) -> evenb (S n) = not (evenb n)
evenb_S Z = Refl
evenb_S (S Z) = Refl
evenb_S (S (S n)) =
  let rec = evenb_S n in
  rewrite rec in Refl

mult_0_plus' : (n, m : Nat) -> (0 + n) * m = n * m
mult_0_plus' Z Z = Refl
mult_0_plus' Z (S k) = Refl
mult_0_plus' (S k) Z = Refl
mult_0_plus' (S k) (S j) = let rec = mult_0_plus' k j in Refl
-- or with Elab
-- mult_0_plus' = %runElab (proofByInductionOnNat' (intro `{{m}}))

plus_k_Sj : (k, j : Nat) -> k + (S j) = j + (S k)
plus_k_Sj Z Z = Refl
plus_k_Sj Z (S k) = rewrite plus_1_1 k in Refl
plus_k_Sj (S k) Z = rewrite plus_1_1 k in Refl
plus_k_Sj (S k) (S j) =
  let rec = plus_k_Sj k j in
  rewrite plus_comm k (S (S j)) in
  rewrite plus_comm j (S (S k)) in
  rewrite plus_comm j k in Refl

plus_rearrange : (n, m, p, q : Nat) -> (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange Z Z Z Z = Refl
plus_rearrange Z Z Z (S k) = Refl
plus_rearrange Z Z (S k) q = Refl
plus_rearrange Z (S k) Z q = rewrite plus_n_0 k in Refl
plus_rearrange Z (S k) (S j) q = rewrite plus_n_0 k in Refl
plus_rearrange (S k) Z p q = rewrite plus_n_0 k in Refl
plus_rearrange (S k) (S j) p q = rewrite plus_k_Sj j k in Refl
