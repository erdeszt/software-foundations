Require Export Basics.

Inductive natprod : Type :=
  pair (n1 n2 : nat).
  
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
  
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y 
  end.
  
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | pair x y => pair y x
  end.
  
Notation "( x , y )" := (pair x y).

Theorem surjective_pairing : forall n m : nat,
  (n, m) = (fst (n, m), snd (n, m)).
Proof. intros. simpl. reflexivity. Qed.

Theorem surjective_pairing' : forall p : natprod,
  p = (fst p, snd p).
Proof. intros. destruct p as [x y]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall p : natprod,
  (snd p, fst p) = swap_pair p.
Proof. intros. destruct p as [x y]. simpl. reflexivity. Qed.

Theorem fst_swap_is_snd : forall p : natprod,
  fst (swap_pair p) = snd p.
Proof. intros. destruct p as [x y]. simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
  
Notation "x :: l" := (cons x l) 
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: _ => h
  end.
  
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | _ :: t => t
  end.
  
Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | n :: t => n :: nonzeros t
  end.

Example test_nonzeros : nonzeros [0; 1; 0; 2; 3; 0; 0] = [1 ; 2; 3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
    match oddb h with
    | true => h :: oddmembers t
    | false => oddmembers t
    end
  end.
  
Example test_oddmembers : oddmembers [0; 1; 0; 2; 3; 0; 0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l : natlist) : nat := length (oddmembers l).

Example test_countoddmembers1:  countoddmembers [1; 0; 3; 1; 4; 5] = 4.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, nil => nil
  | h1 :: t1, nil => h1 :: t1
  | nil, h2 :: t2 => h2 :: t2
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.
  
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
    if eqb v h
      then 1 + count v t
      else count v t
  end.
  
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := negb (eqb (count v s) 0).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    if eqb h v
      then t
      else h :: remove_one v t
  end.
  
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    if  eqb h v
      then remove_all v t
      else h :: remove_all v t
  end.
  
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | nil => true
  | h :: t =>
    if member h s2
      then subset t (remove_one h s2)
      else false
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem eqb_reflexive : forall n : nat, n =? n = true.
Proof.
  intros.
  induction n as [| n' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem count_add_S : forall (b : bag) (n : nat),
  S (count n b) = count n (add n b).
Proof.
  intros.
  induction b as [| h t ].
  - simpl. rewrite eqb_reflexive. reflexivity.
  - simpl. rewrite eqb_reflexive. reflexivity.
Qed.

Theorem nil_app : forall l : natlist, [] ++ l = l.
Proof. intros. simpl. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| n l' ].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.











