Require Export Basics.

Theorem plus_n_O : forall n : nat,
  n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n : nat,
  minus n n = 0.
Proof.
  induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n as [|n].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n as [|n].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n as [|n].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.
  
Compute double 2.

Lemma double_plus : forall n : nat, double n = n + n.
Proof.
  intros.
  induction n as [|n].
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros.
  induction n as [| n' IHn' ].
  - simpl. reflexivity.
  - rewrite IHn'. rewrite negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros.
  assert (H : 0 + n = n). { reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem plus_rearrange_firs : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  rewrite (plus_comm n m).
  reflexivity.
Restart.
  intros.
  assert (H : n + m = m + n).
    { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

