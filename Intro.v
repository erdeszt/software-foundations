Module Datatypes.

Inductive bool : Type := true | false.

(* Scala:
  sealed trait Bool
  case class True() extends Bool
  case class False() extends Bool
*)

(* Unary natural numbers (Peano number) *)
Inductive nat : Type :=
| O 
| S (n : nat).

(* Scala:
  sealed trait Nat
  case class O() extends Nat
  case class S(n: Nat) extends Nat
*)

(* Built in support for naturals(and booleans) *)
Check (S (S (S O))).
Check 1.

End Datatypes.
(****************************************************)

Module Functions.

Definition negate (b : bool) : bool :=
  match b with
  | true  => false
  | false => true
  end.

(* Scala:
  def negate(b: Bool): Bool = {
    b match {
      case True()  => False()
      case False() => True()
    }
  }
*)

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O    => m
  | S n' => S (plus n' m)
  end.

(* Scala:
  def plus(n: Nat)(m: Nat): Nat = {
    n match {
      case O() => m
      case S(pred) => S(plus(pred)(m))
    }
  }
*)

End Functions.

(****************************************************)

Module Tests.

Example negate_true : negb true = false.
Proof. simpl. reflexivity. Qed.

Example four_plus_5 : 4 + 5 = 9.
Proof. simpl. reflexivity. Qed.

End Tests.

(****************************************************)

Module Proofs.

Theorem left_identity : forall (n : nat),
  0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem right_identity : forall (n : nat),
  n + 0 = n.
Proof.
  intros.
  simpl.
  unfold plus.
Restart.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. try reflexivity. rewrite IHn. reflexivity.
Qed.

Theorem plus_assoc : forall (n m o : nat),
  n + (m + o) = (n + m) + o.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_comm : forall (n m : nat),
  n + m = m + n.
Proof.
  intros.
  induction n.
  - simpl. rewrite right_identity. reflexivity.
  - simpl. rewrite IHn.
    Search plus.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

End Proofs.

(****************************************************)

Module Categories.

Class Category (CAT : Type -> Type -> Type) : Type :=
{
  id : forall {A : Type}, CAT A A;
  compose : forall {A B C : Type}, CAT B C -> CAT A B -> CAT A C;
}.

(* Scala:
  trait Category[CAT[_, _]] {
    def id[A]: CAT[A, A]
    def compose[A, B, C](bc: CAT[B, C], ab: CAT[A, B]): CAT[A, C]
  }
*)

Class CorrectCategory (CAT : Type -> Type -> Type) (E : Category CAT) : Type := 
{
  category_left_identity : forall {A B : Type} {f : CAT A B}, 
    compose f id = f;

  category_right_identity : forall {A B : Type} {f : CAT A B}, 
    compose id f = f;

  category_associativity : forall {A B C D : Type} {f : CAT C D} {g : CAT B C} {h : CAT A B},
    compose f (compose g h) = compose (compose f g) h;
}.

(* Type alias *)
Definition Fn (A B : Type) := A -> B.

Instance fnCategory : Category Fn :=
{
  id A := fun a => a;
  compose A B C f g a := f (g a);
}.

(* Scala:
  implicit val fnCategory: Category[Function1] = new Category[Function1] {
    def id[A]: CAT[A, A] = (a: A) => a
    def compose[A, B, C](bc: Function1[B, C], ab: Function1[A, B]): Function1[A, C] = {
      (a: A) => bc.apply(ab.apply(a))
    }
  }
*)

Theorem fn_category_left_identity : forall (A B : Type) (f : Fn A B), compose f id = f.
Proof. intros. simpl. reflexivity. Qed.

Theorem fn_category_right_identity : forall (A B : Type) (f : Fn A B), compose id f = f.
Proof. intros. simpl. reflexivity. Qed.

Theorem fn_category_associativity : forall (A B C D : Type) (f : Fn C D) (g : Fn B C) (h : Fn A B),
  compose f (compose g h) = compose (compose f g) h.
Proof. intros. simpl. reflexivity. Qed.

Instance fnCorrectCategory : CorrectCategory Fn fnCategory :=
{
  category_left_identity := fn_category_left_identity;
  category_right_identity := fn_category_right_identity;
  category_associativity := fn_category_associativity;
}.

Definition kleisli (F : Type -> Type) (A B : Type) : Type := A -> F B.

(* Scala:
  type Kleisli[F[_], A, B] = A => F[B]
  // or as a proper type not just an alias(cats):
  case class Kleisli[F[_], A, B](run: A => F[B])
*)

(* Kleisli is only a category if the F parameter is a Monad
   so we need to defines Monads along with their laws *)

Class Monad (M : Type -> Type) : Type :=
{ 
  pure : forall {A : Type}, A -> M A;
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
}.

Class CorrectMonad (M : Type -> Type) `(E : Monad M) :=
{
  monad_left_identity :
    forall (A B : Type)
           (f : A -> M B)
           {a : A},
    bind (pure a) f = f a;

  monad_right_identity :
    forall {A : Type}
           {m : M A},
    bind m pure = m;

  monad_associativity :
    forall {A B C : Type},
    forall {f : A -> M B}
           {g : B -> M C}
           {m : M A},
    bind (bind m f) g = bind m (fun (a : A) => bind (f a) g);
}.

(* Detour defining a Monad instance for Option and showing it's correctness *)

Instance optionMonad : Monad option :=
{
  pure A x := Some x;
  bind A B ma f := 
    match ma with
      | None   => None
      | Some a => f a
    end;
}.

Theorem option_monad_left_identity : forall (A B : Type) (f : A -> option B) (a : A), bind (pure a) f = f a.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem option_monad_right_identity : forall (A : Type) (m : option A), bind m pure = m.
Proof.
  intros.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem option_monad_associativity : forall (A B C : Type) (f : A -> option B) (g : B -> option C)
    (m : option A), bind (bind m f) g = bind m (fun a : A => bind (f a) g).
Proof.
  intros.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Instance correctOptionMonad : CorrectMonad option optionMonad :=
{
  monad_left_identity := option_monad_left_identity;
  monad_right_identity := option_monad_right_identity;
  monad_associativity := option_monad_associativity;
}.

(* Finally back to Kleisli *)

Instance kleisliCategory (M : Type -> Type) `(Monad M) : Category (kleisli M) :=
{
  id A := pure;
  compose A B C f g a := bind (g a) f;
}.

(* Scala:
  implicit def kleisliCategory[F[_]](implicit M: Monad[F]): Category[Kleisli[F, ?, ?]] = new Category[Kleisli[F, ?, ?]] {
    def id[A]: Kleisli[F, A, A] = Kleisli(a => M.pure(a))
    def compose[A, B, C](f: Kleisli[F, B, C], g: Kleisli[F, A, B]): Kleisli[F, A, C] = {
      Kleisli((a: A) => M.bind(g.run(a))(f.run))
    }
  }
*)

Theorem kleisli_option_category_left_identity : forall (A B : Type) (f : kleisli option A B),
  compose f id = f.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem kleisli_option_category_right_identity : forall (A B : Type) (f : kleisli option A B),
  compose id f = f.
Proof.
  intros.
  simpl.
Admitted.

Theorem kleisli_option_category_associativity : forall (A B C D : Type) (f : kleisli option C D) (g : kleisli option B C)
    (h : kleisli option A B),
  compose f (compose g h) = compose (compose f g) h.
Proof.
  intros.
Admitted.

Instance kleisliOptionCorrectCategory : CorrectCategory (kleisli option) (kleisliCategory option optionMonad) :=
{
  category_left_identity := kleisli_option_category_left_identity;
  category_right_identity := kleisli_option_category_right_identity;
  category_associativity := kleisli_option_category_associativity;
}.

End Categories.

Module Algebra.

Inductive either (A B : Type) : Type :=
| Left (a : A)
| Right (b : B).

Arguments Left {A} {B} _.
Arguments Right {A} {B} _.

Definition prod_to_sum {A B C : Type} (p : A * either B C) : either (A * B) (A * C) :=
  match p with
  | (a, e) => 
    match e with
    | Left b => Left (a, b)
    | Right c => Right (a, c)
    end
  end.

Definition sum_to_prod {A B C : Type} (e : either (A * B) (A * C)) : A * either B C :=
  match e with
  | Left (a, b) => (a, Left b)
  | Right (a, c) => (a, Right c)
  end.

Theorem prod_sum_iso_1 : forall (A B C : Type) (p : A * either B C),
  sum_to_prod (prod_to_sum p) = p.
Proof.
  intros.
  destruct p.
  destruct e.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem prod_sum_iso_2 : forall (A B C : Type) (e : either (A * B) (A * C)),
  prod_to_sum (sum_to_prod e) = e.
Proof.
  intros.
  destruct e.
  - destruct a. simpl. reflexivity.
  - destruct b. simpl. reflexivity.
Qed.

Definition pair_to_either {A : Type} (p : bool * A) : either A A :=
  match p with
  | (true, a) => Right a
  | (false, a) => Left a
  end.

Definition either_to_pair {A : Type} (e : either A A) : bool * A :=
  match e with
  | Right a => (true, a)
  | Left a => (false, a)
  end.

Theorem pair_either_iso_1 : forall (A : Type) (p : bool * A),
  either_to_pair (pair_to_either p) = p.
Proof.
  intros.
  destruct p.
  simpl.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem pair_either_iso_2 : forall (A : Type) (e : either A A),
  pair_to_either (either_to_pair e) = e.
Proof.
  intros.
  destruct e; simpl; reflexivity.
Qed.

Inductive unit := Unit.

Definition bool_to_either (b : bool) : either unit unit :=
  match b with
  | true => Right Unit
  | false => Left Unit
  end.

Definition either_to_bool (e : either unit unit) : bool :=
  match e with
  | Right _ => true
  | Left _ => false
  end.

Theorem bool_iso_either_1 : forall (b : bool),
  either_to_bool (bool_to_either b) = b.
Proof.
  intros.
  destruct b; simpl; reflexivity.
Qed.

Theorem bool_iso_either_2 : forall (e : either unit unit),
  bool_to_either (either_to_bool e) = e.
Proof.
  intros.
  destruct e.
  - destruct a. simpl. reflexivity.
  - destruct b. simpl. reflexivity.
Qed.

End Algebra.

(* NOTES:
  - Software foundations book: https://softwarefoundations.cis.upenn.edu/lf-current/index.html
  - Scalafiddle with full code: https://scalafiddle.io/sf/7Zt8qR5/1
  - What Does It Mean to Be a Number? (Peano numbers): https://www.youtube.com/watch?v=3gBoP8jZ1Is
*)





















