Set Warnings "-notation-overridden,-parsing".
Require Export Poly.
Require Export Coq.Arith.Mult.

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

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros.
  induction l; rewrite H; symmetry; apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
  [a; b] = [c; d] ->
  [c; d] = [e; f] ->
  [a; b] = [e; f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite eq1. rewrite eq2.
  reflexivity.
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite eq1. rewrite eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a; b] = [c; d] ->
  [c; d] = [e; f] ->
  [a; b] = [e; f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c; d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  rewrite eq2. apply eq1.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2 : n = pred (S n)). { reflexivity. }
  rewrite H2.
  rewrite H1.
  simpl.
  reflexivity.
Restart.
  intros n m H.
  injection H.
  intros Hn.
  apply Hn.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H as mo no.
  rewrite mo. rewrite no.
  reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros.
  injection H.
  intros.
  injection H0.
  intros.
  rewrite H4.
  reflexivity.
Restart.
  intros.
  injection H0.
  intros.
  symmetry.
  apply H2.
Qed.

Theorem eqb_0_1 : forall (n : nat),
  0 =? n = true -> n = 0.
Proof.
  intros.
  destruct n as [| n' ] eqn:E.
  - reflexivity.
  - discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros.
  discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  (S n) =? (S m) = b ->
  n =? m = b.
Proof.
  intros.
  simpl in H.
  apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

Lemma O_plus_plus : forall (n : nat),
  0 = n + n -> 0 = n.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl in H. rewrite <- plus_n_Sm in H. discriminate H.
Qed.

Theorem plus_n_n_injective : forall (n m : nat),
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [| n' IHn ].
  - intros m H. destruct m.
    + reflexivity.
    + discriminate.
  - intros m H.
    simpl in H.
    rewrite <- plus_n_Sm in H.
    destruct m.
    + discriminate.
    + simpl in H. rewrite <- plus_n_Sm in H.
      apply S_injective in H.
      apply S_injective in H.
      apply IHn in H.
      rewrite H.
      reflexivity.
Qed.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn ].
  - simpl. intros m eq. destruct m as [| m' ] eqn:E.
    + reflexivity.
    + discriminate eq.
  - simpl. intros m eq. destruct m as [| m' ] eqn:E.
    + discriminate eq.
    + apply f_equal.
      apply IHn.
      injection eq as goal.
      exact goal.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn ].
  - intros m eq.
    destruct m as [| m' ].
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m as [| m' ] eqn:E.
    + discriminate.
    + apply IHn in eq.
      rewrite eq.
      reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' ].
  - simpl. intros n eq. destruct n as [| n' ] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros n eq. destruct n as [| n' ] eqn:E.
    + discriminate eq.
    + apply f_equal.
      apply IHm'.
      injection eq as goal.
      exact goal.
Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n].
  simpl.
  intros H.
  assert (H' : m = n). {
    apply eqb_true. exact H.
  }
  rewrite H'.
  reflexivity.
Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent l.
  induction n.
  - intros l eq. destruct l eqn:E.
    + simpl. reflexivity.
    + discriminate eq.
  - intros l eq. destruct l eqn:E.
    + simpl. reflexivity.
    + apply IHn.
      injection eq.
      intros eq'.
      exact eq'.
Qed.

Definition square (n : nat) := n * n.

Lemma square_mult : forall n m,
  square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m). {
    rewrite mult_comm. apply mult_assoc.
  }
  rewrite H.
  rewrite mult_assoc.
  reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros.
  unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn:E2; reflexivity.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
  end.

Lemma list_cons_eq : forall X (l1 l2 : list X) (x : X),
  l1 = l2 -> x :: l1 = x :: l2.
Proof.
  intros X l1 l2 x H. rewrite H. reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  - destruct l1.
    + reflexivity.
    + intros l2 H. discriminate H.
  - intros l1 l2 H. destruct l1.
    + destruct l2.
      * simpl in H. destruct x. destruct (split l). discriminate H.
      * simpl in H. destruct x. destruct (split l). discriminate H.
    + destruct l2.
      * simpl in H. destruct x. destruct (split l). discriminate H.
      * simpl in H. destruct x. destruct (split l). simpl.
        injection H as eq1 eq2 eq3 eq4.
        rewrite eq1.
        rewrite eq3.
        apply list_cons_eq.
        apply IHl.
        rewrite eq2.
        rewrite eq4.
        reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd : forall(n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:E3.
  apply eqb_true in E3.
  - rewrite E3. simpl. reflexivity.
  - destruct (n =? 5) eqn:E5.
    + apply eqb_true in E5.
      rewrite E5. simpl. reflexivity.
    + discriminate eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
Restart.
  intros f b.
  destruct b eqn:E.
  - destruct (f true) eqn:E1.
    + rewrite E1. rewrite E1. reflexivity.
    + destruct (f false) eqn:E2.
      * rewrite E1. reflexivity.
      * rewrite E2. reflexivity.
  - destruct (f false) eqn:E2.
      * destruct (f true) eqn:E3.
        ** rewrite E3. reflexivity.
        ** rewrite E2. reflexivity.
      * rewrite E2. rewrite E2. reflexivity.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [| n IHn' ].
  - intros. destruct m.
    + reflexivity.
    + simpl. reflexivity.
  - intros. destruct m.
    + simpl. reflexivity.
    + simpl. apply IHn'.
Qed.

Theorem eqb_trans : forall (n m p : nat),
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n.
  induction n as [| n' IHn' ].
  - intros. destruct m eqn:Em.
    + exact H0.
    + destruct p eqn:Ep.
      * simpl. reflexivity.
      * apply H.
  - intros m.
    destruct m eqn:Em.
    + intros. destruct p eqn:Ep.
      * exact H.
      * discriminate H.
    + intros. destruct p eqn:Ep.
      * discriminate H0.
      * apply eqb_true in H0.
        rewrite <- H0.
        exact H.
Restart.
  intros n m p eq1 eq2.
  apply eqb_true in eq1.
  apply eqb_true in eq2.
  rewrite <- eq1 in eq2.
  rewrite eq2.
  apply eqb_refl.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l lf.
  generalize dependent x.
  induction l as [| h l' IHl' ].
  - intros. discriminate H.
  - simpl. destruct (test h) eqn:T.
    + intros. injection H as eq1 eq2.
      rewrite eq1 in T. exact T.
    + intros. apply IHl'. exact H.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => true
  | h :: t => andb (test h) (forallb test t)
  end.

Compute (forallb oddb [1; 2; 3]).
Compute (forallb oddb [1; 3]).

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => false
  | h :: t => orb (test h) (existsb test t)
  end.

Compute (existsb oddb [2; 4; 6]).
Compute (existsb oddb [2; 4; 5]).

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool := negb (forallb (fun x => negb (test x)) l).

Compute (existsb' oddb [2; 4; 6]).
Compute (existsb' oddb [2; 4; 5]).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros.
  induction l.
  - simpl.
    unfold existsb'.
    simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    destruct (test x) eqn:TX.
    + simpl.
      unfold existsb'.
      simpl.
      rewrite TX.
      simpl.
      reflexivity.
    + simpl.
      unfold existsb'.
      simpl.
      rewrite TX.
      simpl.
      reflexivity.
Qed.
