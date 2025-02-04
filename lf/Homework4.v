
From LF Require Export Lists.


Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
 intros l1 l2 l3 l4. induction l1 as [| h t HL].
  -simpl. rewrite app_assoc. reflexivity.
  -simpl. rewrite HL. reflexivity.
Qed.


Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
 intros l1 l2. induction l1 as [| n HL].
  -simpl. reflexivity.
  - destruct n.
    + simpl. rewrite -> IHHL. reflexivity.
    + simpl. rewrite -> IHHL. reflexivity. 
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [| n HS].
  -simpl. reflexivity.
  -destruct n.
    +simpl. rewrite leb_n_Sn. reflexivity.
    +simpl. rewrite IHHS. reflexivity.
Qed.


Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros. rewrite <- (rev_involutive l1). rewrite H. apply rev_involutive.
Qed.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 intros. simpl. rewrite<-eqb_id_refl. reflexivity.
Qed.