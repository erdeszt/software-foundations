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
  intros A B f a.
  simpl.
  reflexivity.
Qed.

Theorem option_monad_right_identity : forall (A : Type) (m : option A), bind m pure = m.
Proof.
  intros A m.
  destruct m as [| a].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem option_monad_associativity : forall (A B C : Type) (f : A -> option B) (g : B -> option C)
    (m : option A), bind (bind m f) g = bind m (fun a : A => bind (f a) g).
Proof.
  intros A B C f g m.
  destruct m as [| a ].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
  
Instance correctOptionMonad : CorrectMonad option optionMonad :=
  { 
    monad_left_identity := option_monad_left_identity;
    monad_right_identity := option_monad_right_identity;
    monad_associativity := option_monad_associativity;
  }.

Class Category (CAT : Type -> Type -> Type) : Type :=
  {
    id : forall {A : Type}, CAT A A;
    compose : forall {A B C : Type}, CAT B C -> CAT A B -> CAT A C;
  }.

Class CorrectCategory (CAT : Type -> Type -> Type) (E : Category CAT) : Type := 
  {
    category_left_identity : forall {A B : Type} {f : CAT A B}, compose f id = f;
    
    category_right_identity : forall {A B : Type} {f : CAT A B}, compose id f = f;

    category_associativity : forall {A B C D : Type} {f : CAT C D} {g : CAT B C} {h : CAT A B},
      compose f (compose g h) = compose (compose f g) h;
  }. 
 
Definition Fn (A B : Type) := A -> B.
 
Instance fnCategory : Category Fn :=
  {
    id A := fun a => a;
    compose A B C f g a := f (g a);
  }.

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
  
Instance kleisliCategory (M : Type -> Type) `(Monad M) : Category (kleisli M) :=
  {
    id A := pure;
    compose A B C f g a := bind (g a) f;
  }.
  
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
  unfold id.
  unfold kleisliCategory.
  unfold pure.
  unfold optionMonad.

  assert (H : (fun x : B => Some x) = pure). {
    simpl. reflexivity.
  }
  rewrite H.
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

