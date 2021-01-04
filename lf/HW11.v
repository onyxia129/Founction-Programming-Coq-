Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.


Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** We then introduce a convenient notation for extending an existing
    map with some bindings. *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).



Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. unfold t_update. extensionality i. unfold eqb_string.
  destruct (string_dec x i) as [HT | HF].
  - reflexivity.
  - reflexivity.
Qed.
  
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. unfold t_update. extensionality i. unfold eqb_string.
  destruct (string_dec x i) as [HT | HF].
  - inversion HT. reflexivity.
  - reflexivity.
Qed.






Module Props.


Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.


End And.


(** **** Exercise: 2 stars, standard (conj_fact) 

    Construct a proof object for the following proposition. *)

Lemma conj_fact_fa : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
Proof.
    intros P Q R.
    intros [Hp Hq]. intros [_ Hr].
    split. apply Hp. apply Hr. Show Proof.
Qed.


Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) => fun(H: P/\Q) =>
     match H with
      | conj Hp _ => fun H0 : Q /\ R => match H0 with
                                   | conj _ Hr => conj Hp Hr
                                   end
      end.

Definition conj_fact' : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) => fun(H1: P/\Q) => fun(H2: Q /\ R) =>
    match H1,H2 with
    | conj Hp _ , conj _ Hr => conj Hp Hr
    end.

Print conj_fact_fa.
Print conj_fact.
Print conj_fact'. 
