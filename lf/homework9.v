Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
From Coq Require Export Lia.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** **** Exercise: 1 star, standard (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros. induction n as [|n' Hn].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply Hn.
Qed.


(*Define a predicate div4 such that (div4 n) is valid if and only if n is divisible by 4.*)

Inductive div4 : nat -> Prop := 
| div4_0 : div4 0
| div4_S4 (n : nat) (H : div4 n) : div4 (S (S (S (S n)))).


Example ex1: div4 0.

Proof. 
  apply div4_0.
Qed.


Example ex2: div4 8.

Proof. 
  apply div4_S4. apply div4_S4. apply div4_0.
 Qed.


(*Definie a predicate divisible such that (divisible n m) is valid 
if and only if n is divisible by m，即n是m的倍数。*)

Inductive divisible : nat -> nat -> Prop := 
| divisible_0_m (m : nat) : divisible 0 m
| divisible_n_m (n : nat) (m : nat) (H : divisible (n - m) m) : divisible n m.


Example exd1 : divisible 0 5.

Proof. 
  apply divisible_0_m.
Qed.


Example exd2 : divisible 21 7.

Proof.
  apply divisible_n_m. simpl.
  apply divisible_n_m. simpl.
  apply divisible_n_m. simpl.
  apply divisible_0_m. 
Qed.