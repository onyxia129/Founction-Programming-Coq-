Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
From Coq Require Export Lia.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).


Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Hn Hm. induction Hm as [| m' Em' IHm'].
    - rewrite plus_O_n in Hn. apply Hn.
    - inversion Hn. apply IHm' in H0. apply H0.
Qed.


Module Playground.
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).
End Playground.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n as [| n' Hn'].
  - apply le_n.
  - apply le_S. apply Hn'.
Qed.


Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H as [|x Ex Hx].
    - apply le_n.
    - apply le_S. apply Hx.
Qed.

Lemma le_Sm_n_m_n : forall m n , S n <= m -> n <= m.
Proof.
  intros. induction H as [| x Hx IHx].
    - apply le_S. apply le_n.
    - apply le_S. apply IHx.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
    - apply le_n.
    - apply le_Sm_n_m_n. apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction a as [|x Hx].
  - simpl. apply O_le_n.
  - simpl. apply  n_le_m__Sn_le_Sm. apply Hx.
Qed.

Theorem le_plus_2 : forall a b,
  a <= b + a.
Proof.
  intros. induction b as [|x Hx].
  - simpl. apply le_n.
  - simpl. apply le_S. apply Hx.
Qed.

Search plus.
(*plus_comm: forall n m : nat, n + m = m + n*)

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros. split.
    - induction H.
      + apply le_plus_l.
      + apply le_S. apply IHle.
    - induction H.
      + apply le_plus_2.
      + apply le_S. apply IHle.
Qed.
