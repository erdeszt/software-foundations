{- NOTES:
  Use -p pruviloj to load the lib
-}

module Induction

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

evenb : Nat -> Bool
evenb Z = True
evenb (S Z) = False
evenb (S (S n)) = evenb n

negb : Bool -> Bool
negb True = False
negb False = True

evenb_S : (n : Nat) -> evenb (S n) = negb (evenb n)
evenb_S Z = Refl
evenb_S (S k) =
  let rec = evenb_S k in
    ?wat

