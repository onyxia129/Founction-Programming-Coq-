(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.



Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End MyNot.




(* Do not modify the following line: *)
Definition manual_grade_for_double_neg_inf : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not in H0. unfold not.
  intros. apply H in H1. apply H0 in H1. destruct H1.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros.
  unfold not. intros. destruct H as [H1  H2].
  apply H2 in H1. apply H1.
Qed.

Lemma dist : forall P Q R : Prop, 

    P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).

Proof. 
  intros.
  destruct H as [Hp H'].
  destruct H' as [Hq | Hr].
  - left. split. apply Hp. apply Hq.
  - right. split. apply Hp. apply Hr.
Qed.
  
  

Lemma dist' : forall P Q R : Prop, 

  (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R).

Proof. 
  intros.
  destruct H as [H1 | H2].
  - destruct H1 as [Hp Hq].
    split. apply Hp. left. apply Hq.
  - destruct H2 as [Hp Hr].
    split. apply Hp. right. apply Hr.
Qed.
(** [] *)
(** **** Exercise: 1 star, advanced (informal_not_PNP) 
Theorem
    Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)

Theorem informal_not_PNP : forall P : Prop,
      ~(P /\ ~P).
Proof.
  intros.
  unfold not.
  intros. destruct H.
  apply H0 in H.
  destruct H.
Qed.
