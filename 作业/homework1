Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End NatPlayground.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.


Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Notation "x + y" := (plus x y).
Notation "x * y" := (mult x y).
Notation "x --" := (pred x)(at level 60).


Fixpoint square (n : nat) : nat :=
  match n with
  | O => O
  | S O => S O
  | S n' => ((square n') --) + 2 * (S n')
  end.

Compute square 5.

Example test_square1 : square 5 = 25.

Proof. reflexivity. Qed.
Example test_square2 : square 15 = 225.

Proof. reflexivity. Qed.






Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition xor (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => match b2 with
            | true => false 
            | false => true 
            end
  | false => match b2 with
            | true => true
            | false => true
            end
  end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "! x" := (negb x) (at level 60).


Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c eqn:Ec.
   - destruct b eqn:Eb.
     +simpl.
      intros H.
      reflexivity.
     +simpl.
      intros H.
      reflexivity.
   - destruct b eqn:Eb.
     + simpl.
       intros H.
       rewrite -> H.
       reflexivity.
     + simpl.
       intros H.
       rewrite -> H.
       reflexivity.
 Qed.


Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b.
  destruct b.
  - simpl.
    intros c.
    intros H. 
    rewrite->H.
    reflexivity.
  - simpl.
    intros c.
    intros H. 
    rewrite->H.
    reflexivity.
Qed.