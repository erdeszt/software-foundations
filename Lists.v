Require Export Basics.
Require Export Induction.

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

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros.
  induction l1 as [| h t IHl1 ].
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Theorem length_app : forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1 as [| h t IHl ].
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros.
  induction l as [| h t IHl ].
  - simpl. reflexivity.
  - simpl. 
    rewrite length_app, plus_comm.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Search plus.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros.
  induction l as [| h t IHl ].
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_single : forall (l : natlist) (n : nat),
  rev l ++ [n] = rev (n :: l).
Proof.
  intros.
  destruct l as [| h t ].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem rev_app_distr : forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [| h1 t1 IHl1 ].
  - simpl. repeat rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1, app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| h t IHl ].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3 ++ l4).
Proof.
  intros.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma cons_app_1 : forall (l t: natlist) (h : nat), (h :: t) ++ l = h :: (t ++ l).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma non_zeros_cons : forall (t : natlist) (h : nat),
  nonzeros (h :: t) = nonzeros [h] ++ nonzeros t.
Proof.
  intros.
  induction h.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1 as [| h1 t1 IHl1 ].
  - simpl. reflexivity.
  - simpl ((h1 :: t1) ++ l2).
    rewrite non_zeros_cons.
    rewrite IHl1.
    rewrite non_zeros_cons.
    assert (H : nonzeros [] = []). {
      simpl. reflexivity.
    }
    rewrite H.
    rewrite app_nil_r.
    assert (H2 : nonzeros (h1 :: t1) = nonzeros [h1] ++ nonzeros t1). {
      rewrite non_zeros_cons. reflexivity.
    }
    rewrite H2. 
    rewrite app_assoc.
    reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | n :: t, nil => false
  | nil, n :: t => false
  | n :: ns, m :: ms => andb (eqb n m) (eqblist ns ms)
  end.
  
Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqb_refl : forall n : nat,
  n =? n = true.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem eqblist_refl : forall l : natlist,
  true = eqblist l l.
Proof.
  intros.
  induction l as [| h t IHl ].
  - simpl. reflexivity.
  - simpl.
    rewrite eqb_refl.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros.
  simpl.
  destruct (count 1 s).
  - reflexivity.
  - reflexivity.
Qed.

Theorem leb_n_Sn : forall n, 
  n <=? (S n) = true.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem remove_does_not_increase_count : forall s : bag,
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros.
  induction s.
  - simpl. reflexivity.
  - destruct n.
    + simpl. rewrite leb_n_Sn. reflexivity.
    + simpl. rewrite IHs. reflexivity.
Qed.


Lemma count_nil : forall n : nat,
  count n [] = 0.
Proof. intros. simpl. reflexivity. Qed.

Lemma sum_nil_r : forall s : bag,
  sum s [] = s.
Proof. 
  intros.
  induction s.
  - simpl. reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.

Lemma if_S : forall (b : bool) (n : nat),
  (if b then 1 else 0) + n = if b then S n else n.
Proof.
  intros.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma count_cons : forall (t : bag) (h n : nat),
  count n (h :: t) = count n [h] + count n t.
Proof.
  intros.
  destruct n.
  - destruct h.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct h.
    + simpl. reflexivity.
    + simpl. rewrite if_S. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n as [|n].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma sum_cons : forall (h : nat) (t s : bag),
  sum (h :: t) s = h :: (sum t s).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem count_sum_distr : forall (s1 s2 : bag) (n : nat),
  count n s1 + count n s2 = count n (sum s1 s2).
Proof.
  intros.
  induction s1 as [| h1 t1 IHs1 ].
  - simpl. reflexivity.
  - rewrite count_cons. 
    rewrite <- plus_assoc.
    rewrite IHs1.
    rewrite sum_cons.
    assert (H : count n (h1 :: sum t1 s2) = count n [h1] + count n (sum t1 s2)). {
      rewrite count_cons. reflexivity.
    }
    rewrite H.
    reflexivity.
Qed.

Theorem rev_nil : rev [] = [].
Proof. simpl. reflexivity. Qed.

(*
Theorem rev_inj : forall l1 l2 : natlist,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  
Admitted.
*)


Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.
  
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  intros.
  destruct x.
  unfold eqb_id.
  assert (H : n =? n = true). {
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Module PartialMap.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
  
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
  
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.
  
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros.
  induction d.
  - simpl. rewrite <- eqb_id_refl. reflexivity.
  - simpl. rewrite <- eqb_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros.
  induction d.
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

End PartialMap.











