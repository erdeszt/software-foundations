Set Warnings "-notation-overridden,-parsing".
Require Export Lists.

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil 
  | S count' => cons x (repeat x count')
  end.
  
Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
  
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
  
Theorem app_nil_r : forall (X : Type), forall (l : list X),
  l ++ [] = l.
Proof.
  intros.
  induction l as [| h t IHn ].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem app_assoc : forall (A : Type) (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l as [| h t IHn ].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1 as [| h1 t1 IHn1 ].
  - simpl. reflexivity.
  - simpl. rewrite IHn1. reflexivity.
Qed.

Theorem rev_app_distr : forall (X : Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [| h1 h2 IHn1 ].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHn1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| h t IHn ].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr.
    simpl. rewrite IHn.
    reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
  
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.
  
Compute (combine [1; 2] [false; false; true; true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil => ([], [])
  | cons (x, y) t => 
    match split t with
    | (xs, ys) => (x :: xs, y :: ys)
    end
  end.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X} _.
Arguments None {X}.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Fixpoint filter {X : Type} (test: X -> bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => 
    if test h 
      then h :: (filter test t)
      else filter test t
  end.

Fixpoint even (n : nat) :=
  match n with
  | O => true
  | S O => false
  | S (S n) => even n
  end.

Fixpoint lteb (n m : nat) :=
  match n, m with
  | O, O => true
  | O, S _ => true
  | S _, O => false
  | S n', S m' => lteb n' m'
  end.
  
Definition gtb (n m : nat) := negb (lteb n m).

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => even n && gtb n 7) l.
  
Example test_filter_even_gt7 :
  filter_even_gt7 [1; 2; 6; 9; 10; 3; 12; 8] = [10; 12; 8].
Proof. reflexivity. Qed.

Definition partition 
  {X : Type}
  (test : X -> bool) 
  (l : list X) : list X * list X :=
  (filter test l, filter (fun a => negb (test a)) l).
  
Example test_partition : partition oddb [1; 2; 3; 4; 5] = ([1; 3; 5], [2; 4]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.
  
Lemma map_last : forall (X Y : Type) (f : X -> Y) (l : list X) (x : X),
  map f (l ++ [x]) = map f l ++ [f x].
Proof.
  intros.
  induction l as [| h t IHn ].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l as [| h t IHn ].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. rewrite map_last. reflexivity.
Qed.
  
Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | h :: t => f h ++ flat_map f t
  end.
  
Example test_flat_map : flat_map (fun n => [n; n; n]) [1; 5; 4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end. 

(* TODO : Fold *)




