Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.

Definition injective {A B} (f : A -> B) :=
  forall (x y : A), f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  injection H as H1.
  apply H1.
Qed.

Check eq.
Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro; reflexivity.
Qed.

Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - induction n.
    + reflexivity.
    + discriminate H.
  - induction m.
    + reflexivity.
    + rewrite <- plus_n_Sm in H.
      discriminate H.
Qed.

Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm. reflexivity.
Qed.

Lemma and_example3 : forall n m : nat,
  n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof. intros P Q H. destruct H as [p q]. apply p. Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof. intros P Q H. destruct H as [p q]. apply q. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split. apply HP. apply HQ.
  - apply HR.
Qed.

Lemma or_example : forall n m : nat,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ : forall n : nat,
  n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem ex_falso_quodlibet : forall P : Prop,
  False -> P.
Proof.
  intros.
  destruct H.
Qed.

Fact not_implies_our_not : forall P : Prop,
  not P -> (forall Q : Prop, P -> Q).
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof. unfold not. intros. discriminate H. Qed.

Theorem not_False : not False.
Proof. unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros.
  apply H0 in H.
  destruct H.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not in H0.
  unfold not.
  intros.
  apply H in H1.
  apply H0 in H1.
  destruct H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intros P [PY PN].
  unfold not in PN.
  apply PN in PY.
  destruct PY.
Qed.

Theorem not_true_is_false : forall b : bool,
  ~(b = true) -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  ~(b = true) -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso. apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HQ HP].
  split.
  apply HP.
  apply HQ.
Qed.

Theorem or_distribute_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros PQR.
    split.
    destruct PQR.
    + left. apply H.
    + destruct H. right. apply H.
    + destruct PQR.
      * left. apply H.
      * destruct H. right. apply H0.
  - intros PQR.
    destruct PQR.
    destruct H.
    + left. apply H.
    + destruct H0.
      * left. apply H0.
      * right. split. apply H. apply H0.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mult_eq_0 : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [| n ].
  - intros m H.
    left. reflexivity.
  - intros [| m ].
    + intros H. right. reflexivity.
    + intros H. simpl in H. discriminate H.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - intro H. apply mult_eq_0. apply H.
  - intro H. apply or_example. apply H.
Qed.

Lemma or_assoc : forall P Q R : Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 : forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0.
  rewrite mult_0.
  rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example : forall n m : nat,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  apply mult_0. apply H.
Qed.

Lemma four_is_even : exists n : nat,
  4 = n + n.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  simpl.
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~(exists x, ~(P x)).
Proof.
  intros X P.
  unfold not at 1.
  intros H1 H2.
  destruct H2 as [x E].
  unfold not in E.
  apply E in H1.
  apply H1.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intro E.
    destruct E as [x EE].
    destruct EE.
    + left. exists x. apply H.
    + right. exists x. apply H.
  - intro E.
    destruct E.
    + destruct H as [x EE].
      exists x. left. apply EE.
    + destruct H as [x EE].
      exists x. right. apply EE.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. simpl. symmetry. apply H.
  - exists 2. simpl. symmetry. apply H.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| h t IHl ].
  - simpl. intros F. apply F.
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + apply IHl in H. right. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
      exists x, f x = y /\ In x l.
Proof.
  intros A B f l x.
  split.
  - intros H. induction l as [| x' l' IHl' ].
    + simpl in H. contradiction.
    + simpl in H. destruct H as [ H1 | H2 ].
      * exists x'. split.
        ** apply H1.
        ** simpl. left. reflexivity.
      * apply IHl' in H2. destruct H2 as [x2 H2]. destruct H2. exists x2. split.
          ** apply H.
          ** simpl. right. apply H0.
  - intros H. induction l as [| h t IHl ].
    + destruct H. destruct H. contradiction.
    + simpl. simpl in H.
      destruct H as [x'' H].
      inversion H.
      destruct H1 as [H2 | H3].
      * left. rewrite H2. apply H0.
      * right. apply IHl.
        exists x''.
        split.
        ** apply H0.
        ** apply H3.
Qed.

Lemma In_cons : forall A l (a x : A),
  In a l -> In a (x :: l).
Proof.
  intros A l a x.
  induction l.
  - intros. simpl in H. contradiction.
  - intros. simpl in H.
    destruct H.
    + rewrite H. simpl.
      right. left. reflexivity.
    + apply IHl in H.
      simpl. simpl in H.
      destruct H.
      * rewrite H. left. reflexivity.
      * right. right. apply H.
Qed.

Lemma In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros.
  split.
  - intros H.
    induction l.
    + simpl. simpl in H. right. apply H.
    + simpl in H.
      destruct H.
      * rewrite H. simpl. left. left. reflexivity.
      * apply IHl in H. destruct H.
        ** left. apply In_cons. apply H.
        ** right. apply H.
  - intros H.
    induction l.
    + destruct H.
      * simpl in H. contradiction.
      * simpl. apply H.
    + destruct H.
      * simpl in H.
        simpl.
        destruct H.
        ** left. rewrite H. reflexivity.
        ** right. apply IHl. left. apply H.
     * simpl. right. apply IHl. right. apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Lemma All_cons : forall T (P : T -> Prop) (x : T) (l : list T),
  All P (x :: l) -> All P l.
Proof.
  intros.
  induction l.
  - simpl. apply I.
  - simpl in H. destruct H. destruct H0.
    simpl. split.
    + apply H0.
    + apply H1.
Qed.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
      All P l.
Proof.
  intros T P l.
  split.
  - induction l.
    + intros H. simpl. apply I.
    + intros H. simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHl. intros. apply H.
        apply In_cons. apply H0.
  - intros H.
    induction l as [| h t IHl ].
    + contradiction.
    + simpl. intros. destruct H0 as [| H1 H2 ].
      * simpl in H. apply proj1 in H. rewrite H0 in H. apply H.
      * simpl in H. apply proj2 in H. apply IHl.
        ** apply H.
        ** apply H1.
Qed.

Check plus_comm.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> not (l = []).
Proof.
  intros A x l H.
  unfold not.
  intro Hl.
  destruct l.
  - simpl in H. contradiction.
  - discriminate Hl.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> not (l = []).
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Restart.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mult_0_r in Hm.
  rewrite <- Hm. reflexivity.
Qed.

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X := rev_append l [].

Lemma rev_append_app : forall X (l1 l2 : list X),
  rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros X l1.
  induction l1 as [| h t IHl1 ].
  - simpl. reflexivity.
  - intros l2. destruct l2.
    + simpl. rewrite IHl1. rewrite app_nil_r. reflexivity.
    + simpl. rewrite IHl1. rewrite  <- app_assoc. simpl. reflexivity.
Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @Poly.rev X.
Proof.
  intros.
  apply functional_extensionality.
  intros l.
  unfold tr_rev.
  rewrite rev_append_app.
  apply app_nil_r.
Qed.

Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

Example even_42_props : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros.
  induction k as [| k' IHk ].
  - simpl. reflexivity.
  - simpl. apply IHk.
Qed.

Theorem evenb_S_double : forall k, evenb (S (double k)) = false.
Proof.
  intros.
  induction k as [| k' IHk' ].
  - simpl. reflexivity.
  - apply IHk'.
Qed.

Require Export Induction.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k else S (double k).
Proof.
  intros n.
  induction n as [| n' IHn ].
  - simpl. exists 0. reflexivity.
  - rewrite  evenb_S.
    destruct (evenb n') eqn:E.
    + destruct IHn as [k']. rewrite H. exists k'. simpl. reflexivity.
    + destruct IHn as [k']. rewrite H. exists (S k'). simpl. reflexivity.
Qed.


Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n.
  split.
  - intros. destruct (evenb_double_conv n) as [k Hk]. rewrite Hk. rewrite H. exists k. reflexivity.
  - intros. destruct (evenb_double_conv n) as [k Hk]. destruct H. rewrite H. apply evenb_double.
Qed.




















