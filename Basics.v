Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d : day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday : 
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true  => false
  | false => true
  end.
  
Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true  => b2
  | false => false
  end.
Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true  => true
  | false => b2
  end.

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  negb (andb b1 b2).

Definition nandb2 (b1 : bool) (b2 : bool) : bool :=
  match b1 with
    | true  => negb b2
    | false => true
  end.

Example test_nandb1 : (nandb true false) = true.
Proof. unfold nandb. simpl. trivial. Qed.

Example test_nandb1_2 : (nandb2 true false) = true.
Proof. simpl. reflexivity. Qed.

Theorem nandb1_eqv_nandb2 : forall (b1 : bool) (b2 : bool), nandb b1 b2 = nandb2 b1 b2.
Proof.
  intros.
  induction b1.
    - simpl.
      unfold nandb.
      simpl.
      reflexivity.
    - unfold nandb.
      simpl.
      reflexivity.
Qed.

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool): bool :=
  andb b1 (andb b2 b3).

Example test_andb31 : (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32 : (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33 : (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34 : (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check negb.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).
  
Definition pred (n : nat) : nat :=
  match n with
    | O    => O
    | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
    | O    => O
    | S O  => O
    | S n' => n'
  end.
  
Fixpoint evenb (n : nat) : bool :=
  match n with
    | O        => true
    | S O      => false
    | S (S n') => evenb n'
  end.
  
Definition oddb (n : nat) : bool := negb (evenb n).

Example test_odd1 : oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O    => m
    | S n' => S (plus n' m)
  end.
  
Compute (plus 2 3).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O    => O
    | S n' => plus m (mult n' m)
  end.
  
Example test_mult1 : (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
    | O , _      => O
    | S _ , O    => n
    | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O   => S O
    | S p => mult base (exp base p)
  end.
  
Fixpoint factorial (n : nat) : nat :=
  match n with
    | O    => S O
    | S n' => mult n (factorial n')
  end.
  
Example test_factorial1 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2 : (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool := 
  match n, m with
    | O   , O    => true
    | S _ , O    => false
    | O   , S _  => false
    | S n', S m' => eqb n' m'
  end.
  
Fixpoint leb (n m : nat) : bool :=
  match n, m with
    | O   , O    => true
    | O   , S _  => true
    | S _ , O    => false
    | S n', S m' => leb n' m'
  end.

Definition ltb (n m : nat) : bool := leb n m && negb (eqb n m).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Example test_ltb1 : (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2 : (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3 : (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros n_eq_m.
  rewrite n_eq_m.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros n_eq_m.
  intros m_eq_o.
  rewrite n_eq_m.
  rewrite m_eq_o.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros m_eq_Sn.
  rewrite -> m_eq_Sn.
  reflexivity.
Qed.

Theorem plus_1_neg_0 : forall n : nat, 
  (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem plus_1_neg_0' : forall n : nat, (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  - simpl. intros p. exact p.
  - simpl. intros p. discriminate.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
      forall (b : bool), f (f b) = b.
Proof.
  intros f f_id b.
  rewrite f_id.
  rewrite f_id.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) ->
      forall (b : bool), f (f b) = b.
Proof.
  intros f f_negb b.
  rewrite f_negb.
  rewrite f_negb.
  rewrite negb_involutive.
  reflexivity.
Qed.

Theorem andb_eq_orb : 
  forall (b c : bool), 
    (andb b c = orb b c) -> b = c.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
Restart.
  intros b c.
  destruct b.
  - simpl. intros p. symmetry in p. exact p.
  - simpl. intros p. exact p.
Qed.

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint bin_to_nat' (m : bin) (pow : nat) : nat :=
  match m with
    | Z => O
    | B n => exp 2 pow + bin_to_nat' n (S pow)
    | A n => bin_to_nat' n (S pow)
  end.
  
Definition bin_to_nat (m : bin) : nat :=
  bin_to_nat' m 0.
  
Compute bin_to_nat Z.
Compute bin_to_nat (B Z).
Compute bin_to_nat (A (B Z)).
Compute bin_to_nat (B (B Z)).
Compute bin_to_nat (A (A (B Z))).
Compute bin_to_nat (B (B (B Z))).
Compute bin_to_nat (A (A (A (B Z)))).

Fixpoint incr (m : bin) : bin :=
  match m with
    | Z => B Z
    | B Z => A (B Z)
    | A n => B n
    | B n => A (incr n)
  end.
  
Compute bin_to_nat (incr Z). (* S 0 *)
Compute bin_to_nat (incr (B Z)). (* S 1 *)
Compute bin_to_nat (incr (A (B Z))). (* S 2 *)
Compute bin_to_nat (incr (B (B Z))). (* S 3 *)
Compute bin_to_nat (incr (A (A (B Z)))). (* S 4 *)
Compute bin_to_nat (incr (B (B (B Z)))). (* S 7 *)
Compute bin_to_nat (incr (A (A (A (B Z))))). (* S 8 *)














