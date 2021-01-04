From LF Require Export Basics.
From LF Require Export Induction.
From LF Require Export Lists.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition bag := natlist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with 
  | nil =>  O
  | h :: t => if (h =? v) then S(count v t) else count v t
  end.



(*作业*)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
 match s with
  |nil => s
  |h::t => if(h =? v) then t else h::(remove_one v t)
 end.

Compute remove_one 1 [2;1;3;1;4;1].

Example test_remove : remove_one 1 [2;1;3;1;4;1] = [2;3;1;4;1]. 

Proof. reflexivity. Qed.

Compute count 5 (remove_one 5 [2;1;5;4;1]).

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.




Fixpoint replace_one (n m:nat)(l:natlist) : natlist :=
  match l with
  |nil => l
  |h :: t => if (n=?h) then m :: t else h :: (replace_one n m t)
  end.

Compute replace_one 1 5 [2;1;3;1;4;1].

Example test_replace : replace_one 1 5 [2;1;3;1;4;1] = [2;5;3;1;4;1]. 

Proof.  reflexivity. Qed.

Fixpoint insert (n:nat)(l:natlist) : natlist :=
  match l with
  |nil => n::nil
  |h :: t => if (h <=? n) then h:: (insert n t) else n::h::t
  end.

Compute insert 5 [1;3;4;6;6].

Example test_insert : insert 5 [1;3;4;6;6] = [1; 3; 4; 5; 6; 6]. 

Proof.  reflexivity. Qed.

Fixpoint insertion_sort (l:natlist) : natlist  :=
  match l with
  | nil => nil
  | h :: t => insert h (insertion_sort t)
  end.

Compute insertion_sort [2;4;1;6;9;6;4;1;3;5;10].


Example test_insertion_sort : insertion_sort [2;4;1;6;9;6;4;1;3;5;10] = [1;1; 2; 3; 4; 4; 5; 6; 6; 9; 10]. 
Proof.  reflexivity. Qed.