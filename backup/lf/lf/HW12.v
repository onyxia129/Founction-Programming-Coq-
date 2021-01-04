Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.
Definition relation (X: Type) := X -> X -> Prop.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Print le.

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo.  Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
   intros. inversion H.
    - apply le_n.
    - apply le_Sn_le in H1. apply H1.
Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  unfold not. intros. 
  induction n.
  - inversion H.
  - apply IHn. inversion H.
    + apply H.
    + apply le_trans with (S (S n)).
      * apply le_S. apply le_n. 
      * apply H1.
Qed.


Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric.
  intros.
  assert (1 <= 0).
  - apply H. apply le_S. apply le_n.
  - inversion H0.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercise: 2 stars, standard, optional (le_antisymmetric)  *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a. induction a.
  - intros. inversion H.
    + reflexivity.
    + rewrite H2. rewrite <- H2 in H0. inversion H0.
  - intros. destruct b.
    + inversion H.
    + f_equal. apply IHa.
      * apply le_S_n. apply H.
      * apply le_S_n. apply H0.
Qed.



Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros. induction H.
  - apply H0.
  - apply IHclos_refl_trans_1n in H0. apply rt1n_trans with y.
    + apply Hxy.
    + apply H0.
Qed.