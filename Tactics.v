Set Warnings "-notation-overridden,-parsing".
Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
  n = m ->
  [n; o] = [n; p] ->
  [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (forall (q r : nat), q = r -> [q; o] = [r; p]) ->
  [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex : 
  (forall (n : nat), evenb n = true -> oddb (S n) = true) ->
  oddb 3 = true ->
  evenb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq2.
Qed.

Theorem silly3 : forall (n : nat),
  true = (n =? 5) ->
  (S (S n)) =? 7 = true.
Proof.
  intros.
  symmetry.
  apply H.
Qed.

