(* Final Exam (Paper A) --- January 4, 2021 *)
Require Import Nat.
Require Import List.
From Coq Require Import Bool.Bool.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition admit {T: Type} : T.  Admitted.

(* 1. Prove the following fact about natural numbers. 
Hint: You may search and use some properties about the plus function 
in the standard library of Coq. *)

Search  plus.
(*PeanoNat.Nat.add_1_r: forall n : nat, n + 1 = S n*)
(*PeanoNat.Nat.add_succ_l: forall n m : nat, S n + m = S (n + m)*)
(*PeanoNat.Nat.add_comm: forall n m : nat, n + m = m + n*)
(*PeanoNat.Nat.add_assoc: forall n m p : nat, n + (m + p) = n + m + p*)



Lemma mul_3_r : forall n : nat, n * 3 = n + n + n.
Proof. 
  intros. induction n as [|n' Hn'].
  - simpl. reflexivity.
  - auto. simpl. rewrite Hn'. rewrite <- PeanoNat.Nat.add_1_r. simpl. 
    rewrite <- PeanoNat.Nat.add_1_r. simpl. rewrite <- PeanoNat.Nat.add_1_r. simpl. 
    symmetry. simpl.
    rewrite <- PeanoNat.Nat.add_1_r. simpl. remember (S n'). rewrite (PeanoNat.Nat.add_comm n' n).
    rewrite Heqn. simpl. rewrite <- PeanoNat.Nat.add_1_r. simpl. remember (S n'). 
    rewrite (PeanoNat.Nat.add_comm  (n' + n') n0). rewrite Heqn0. rewrite <- PeanoNat.Nat.add_1_r.
    rewrite  (PeanoNat.Nat.add_assoc (n' + 1) n' n'). simpl. remember (n' + 1).
    rewrite (PeanoNat.Nat.add_comm n1 n'). rewrite (PeanoNat.Nat.add_comm (n' + n1) n').
    rewrite (PeanoNat.Nat.add_assoc n' n' n1). rewrite Heqn1.
    rewrite (PeanoNat.Nat.add_assoc (n'+n') n' 1). reflexivity.
Qed.




(* 2. Complete the following definition so that (div2021 n) returns true 
iff n is divisible by 2021. 
Hint: You may find the leb function useful. *)


Fixpoint div2021 (n : nat ) : bool :=
 match n with 
  | O => true
  | S n' => if ( 2021 <=? S n' ) then div2021 ( S n' - 2021)  else false
end.

Compute div2021 2021.

Example div2021_test1: div2021 4042 = true.
Proof. reflexivity. Qed.

Example div2021_test2: div2021 2027 = false.
Proof. reflexivity. Qed.


(* 3. Define a function createList such that (createList n) returns 
a list of numbers in the form: [n;(n-1);...;2;1;2;...;(n-1);n], for any n > 0. *)

Search app.
Search rev.

Fixpoint app (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Fixpoint rev (l:list nat) : list nat :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Fixpoint repeat (n  : nat) : list nat :=
  match n with
  | O => nil
  | S n' => S n' :: (repeat n')
  end.

Definition removeHead (l:list nat) : list nat :=
match l with
  | nil => nil
  | h::t => t
end.

Compute  app  (repeat 3)  (removeHead (rev( repeat 3))).

Definition createList (n : nat) : list nat :=
  app  (repeat n)  (removeHead (rev( repeat n))).
    
  Compute createList 6 .

Example createList_test : createList 6 = [6;5;4;3;2;1;2;3;4;5;6].
Proof. reflexivity. Qed. 



(* 4. Let oddn and evenn be the predicates that test whether a given number
is odd or even. Show that the sum of an odd number with an even number is odd. *)

Inductive oddn : nat -> Prop :=
 | odd1 : oddn 1
 | odd2 : forall n, oddn n -> oddn (S (S n)).

Inductive evenn : nat -> Prop :=
 | even1 : evenn 0
 | even2 : forall n, evenn n -> evenn (S (S n)).

Theorem odd_add : forall n m, oddn n -> evenn m -> oddn (n + m).
Proof.
 intros. induction H .
  - simpl. induction H0 .
    + constructor.
    + repeat constructor. auto.
  - simpl. induction H0 .
    + simpl. constructor. auto.
    + simpl. repeat constructor. auto.
Qed.




(* 5. Write a function (partition):

      partition : list nat -> list (list nat )

   which partitions a list into a list of 3 sublists. The first sublist
   contains all even numbers in the original list. The second sublist 
   contains all odd numbers divisible by 5 in the original list. The last 
   sublist contains all other elements. The order of elements in the
   three sublists should be the same as their order in the original list. 

   Hint: You may use the Coq function (filter).
*)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool :=
  negb (evenb n).

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Fixpoint div5 (n : nat ) : bool :=
 match n with 
  | O => true
  | S n' => if ( 5 <=? S n' ) then div5 ( S n' - 5)  else false
end.

Fixpoint notdiv5 (n : nat ) : bool :=
 match n with 
  | O => false
  | S n' => if ( 5 <=? S n' ) then notdiv5 ( S n' - 5)  else true
end.

Compute div5 15.

Compute filter evenb [1;2;3;9;4;5;6;15;8].

Compute (filter evenb [1;2;3;9;4;5;6;15;8]) :: (filter oddb [1;2;3;9;4;5;6;15;8]) :: nil.

Compute filter oddb [1;2;3;9;4;5;6;15;8].

Compute filter    div5 ( filter oddb [1;2;3;9;4;5;6;15;8]).

Compute filter    notdiv5 ( filter oddb [1;2;3;9;4;5;6;15;8]).


Definition partition (l : list nat) : list (list nat) :=
 ( filter evenb l) :: ( filter    div5 ( filter oddb l)) :: ( filter notdiv5 ( filter oddb l)) :: nil.

Example partition_test: partition [1;2;3;9;4;5;6;15;8] = [[2;4;6;8]; [5;15]; [1;3;9]].
Proof. reflexivity. Qed.



(* 6. Prove the following fact about excluded middle. *)

Lemma sss : forall P Q : Prop, ~ P -> ~ P \/ Q.
Proof.
intros. left. auto.
Qed.

Search (_ -> False).

Theorem excluded_middle : 
  (forall P Q : Prop, (P -> Q) -> (~P \/ Q)) -> (forall P, P \/ ~P).
Proof. 
  intros.  specialize (H P). right. unfold not. intros.  

Admitted.

(* 7. Let a sequence of numbers F(n) be given as follows.
   F(0) = 0
   F(n) = F(n-1) + 2 * n   for n > 0.

Define the function Seq such that (Seq n) returns the sequence

[0; F(1); 2; F(3); 4; F(5); ... ; 2n; F(2n + 1)].
*)

Fixpoint func (n:nat):nat:=
  match n with
  | O => O
  | S n' => 2*n + (func n')
end.

Fixpoint repeat' (n  : nat) : list nat :=
  match n with
  | O => nil
  | S n' => func( S n') :: (repeat' (n' -1))
  end.

Fixpoint repeat'' (n  : nat) : list nat :=
  match n with
  | O => nil
  | S n' => S n' :: (repeat'' (n'-1))
  end.


(*n = 5*)

Compute rev (repeat' (2*5+1)).

Compute rev (repeat'' (2*5)).

Fixpoint alternate (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | nil , nil => nil
  | nil , _ => l2
  | _ , nil => l1
  | h::t , n::m => h::n::alternate t m
  end.

Compute alternate (rev (repeat' (2*5+1))) (rev (repeat'' (2*5))).

Definition Seq (n: nat) : list nat :=
 0 :: alternate (rev (repeat' (2*n+1))) (rev (repeat'' (2*n))).

Example Seq_test :  Seq 5 = [0; 2; 2; 12; 4; 30; 6; 56; 8; 90; 10; 132].
Proof. reflexivity. Qed. 



(* 8. Consider the following type:

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

Define a function taking as argument a tree t: btree and returning 
the sum of all numbers occurring in the tree. *)

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

Compute leaf 4.



Fixpoint sum (t: btree) : nat :=
 match t with
  | leaf n  => n 
  | node n' p q => n' + (sum p) + (sum q)
end.

Compute sum (node 7 (leaf 6) (leaf 8)).

Example bt_test : sum (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
                              (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
                  = 55.
Proof. reflexivity. Qed.



(* 9. Write in Coq a function that rotates a list. Namely, the call to
(rotate l) returns a new list that is the same as l except that the last 
element of l instead appears as the first element of the new list. *)

Definition hd (default:nat) (l:list nat) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Compute rev [1;2;3;4;5].

Compute hd 0 (rev [1;2;3;4;5]).

Compute removeHead (rev [1;2;3;4;5]).

Compute rev (removeHead (rev [1;2;3;4;5])).

Compute  (hd 0 (rev [1;2;3;4;5])) ::(rev (removeHead (rev [1;2;3;4;5]))).

Definition rotate (l : list nat) : list nat :=
(hd 0 (rev l)) ::(rev (removeHead (rev l))).

Example rotate_test : rotate [1;2;3;4;5] = [5;1;2;3;4].
Proof. reflexivity. Qed.



(* 10. The following definitions specify the abstract syntax of
    some arithmetic expressions and an evaluation function. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* Suppose we define a function that takes an arithmetic expression 
   and slightly simplifies it, changing every occurrence of [e + 0]
   and [e - 0] into just [e], and [e * 1] into [e]. *)

Fixpoint optimize (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus  (ANum 0) e2   => optimize e2
  | APlus  e1 e2 => APlus  (optimize e1) (optimize e2)
  | AMinus (ANum 0) e2  => optimize e2
  | AMinus e1 e2 => AMinus (optimize e1) (optimize e2)
  | AMult  (ANum 1) e2    => optimize e2
  | AMult  e1 e2 => AMult  (optimize e1) (optimize e2)
  end.

(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)

Theorem optimize_mult1_sound: forall a,
  aeval (optimize a) = aeval a.
Proof. 
  intros a. induction a.
  - reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. simpl in IHa1.
Admitted.
 
