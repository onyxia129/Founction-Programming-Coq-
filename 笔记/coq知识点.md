# 知识点

# Basics.v

## 数据与函数

- 检验方式
    - Compute; Eg. Compute (next_weekday friday).
    - Example; Eg. Example test_next_weekday: (next_weekgay (next_weekday saturday)) = tuesday.

        定义好断言后，可以用coq来验证：Proof. simpl. reflexivity. Qed.

- 布尔值
    - negb：非
    - andb：与
    - orb：或
    - andb3：所有输入均为 true 时返回 true，否则返回 false
- Notation：为既有的定义赋予新的中缀记法
    - Notation "x && y" := (andb x y).
    - Notation "x || y" := (orb x y).
- Check
    - 让Coq显示一个表达式的类型
    - 检查以前声名的引理和定理
- 数值
    - 0是一个自然数
    - S可被放在一个自然数之前产生另一个自然数
    - minustwo：减 2
    - evenb：判断是否为偶数
    - oddb：判断是否为基数
    - plus：计算 m + n
    - mult：计算 m * n
    - minus：计算 n - m
    - exp：计算 $base^{power}$
    - factorial：计算斐波那契数列
    - eqb：测试自然数nat间相等关系eq
    - leb：检查第一个参数是否小于等于第二个参数
    - ltb：检查自然数间的小于关系
        - Definition ltb (n m : nat) : bool := leb (S n) m.

## 基于化简的证明

Coq中关键词Example 和 Theorem（以及其它一些，包括 Lemma、Fact 和 Remark）都表示完全一样的东西

```cpp
Theorem plus_O_n : ∀ n : nat, 0 + n = n.
Theorem plus_1_l : ∀ n:nat, 1 + n = S n.
Theorem mult_0_l : ∀ n:nat, 0 × n = 0.
```

## 基于改写的证明

- rewrite：rewrite 中的箭头与蕴含无关：它指示 Coq 从左往右地应用改写。 若要从右往左改写，可以使用 rewrite <-

```cpp
Theorem mult_n_1: ∀ n : nat, n × 1 = n.
Theorem negb_involutive : ∀ b : bool, negb (negb b) = b.
Theorem andb_commutative : ∀ b c, andb b c = andb c b.
Theorem andb3_exchange : ∀ b c d, andb (andb b c) d = andb (andb b d) c.
Theorem andb_true_elim2 : ∀ b c : bool, andb b c = true → c = true.
```

## 利用情况分析来证明

- destruct：分别对n = 0 和 n = S n' 这两种情况进行分析的策略
    - 证明时需要使用元素 n 的具体结构，可以考虑使用 destruct
    - 布尔类型也可以考虑使用 destruct，也可以直接写成 intros [].
    - destruct 策略可用于对任何计算结果进行情况分析
- destruct... eqn:...：为添加到上下文中的等式指定名字， 记录情况分析的结果

## 进制转换

```cpp
Fixpoint incr (m:bin) : bin  //加操作
Fixpoint bin_to_nat (m:bin) : nat //二进制转常数制
Fixpoint nat_to_bin (n:nat) : bin //常数制转二进制
Theorem nat_bin_nat_incr : forall n,
				 bin_to_nat (incr n) = 1 + bin_to_nat n.
```

# Induction.v 归纳证明

## 归纳法证明

其实就是数学归纳法：induction n as [| n' IHn'].

[ ]中第一部分为空，代表初始条件；第二部分为假设 n' 成立，证明 S n' (式子为IHn')也成立

**有时候需要 induction 的时候，可以先对m/n等先 induction，再证明**

- *自然数：要么是 0，要么是 S 应用到某个 “更小” 的自然数上*
- *列表：要么是 nil，要么是 cons 应用到某个数字和某个“更小”的列表上*
- *布尔值：true / false*

要注意 induction 和 intros 的内容，有时候不能一下子都 intros.

```cpp
Theorem mult_0_r : ∀ n:nat, n × 0 = 0.
Theorem plus_n_Sm : ∀ n m : nat, S (n + m) = n + (S m).
Theorem plus_comm : ∀ n m : nat, n + m = m + n.
Theorem plus_assoc : ∀ n m p : nat, n + (m + p) = (n + m) + p.
Theorem evenb_S : ∀ n : nat, evenb (S n) = negb (evenb n).
```

## 证明里的证明

简单地陈述并立即证明所需的“子定理”，使用 assert 策略。

举例：assert (H: 0 + n = n). { reflexivity. }，也可以改写成assert (0 + n = n) as H.

assert 策略引入两个子目标，第一个是断言本身，加前缀 H 将其命名为 H 。在第二个子目标中，可以用已断言的事实在一开始尝试证明的事情上取得进展。

```cpp
Theorem mult_0_plus' : ∀ n m : nat, (0 + n) × m = n × m.
Theorem plus_rearrange : ∀ n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
```

## 更多练习

```cpp
Theorem plus_swap : ∀ n m p : nat, n + (m + p) = m + (n + p).
Theorem mult_comm : ∀ m n : nat, m × n = n × m.
Theorem andb_false_r : ∀ b : bool, andb b false = false.
Theorem mult_1_l : ∀ n:nat, 1 × n = n.
Theorem mult_plus_distr_r : ∀ n m p : nat, (n + m) × p = (n × p) + (m × p).
Theorem mult_assoc : ∀ n m p : nat, n × (m × p) = (n × m) × p.
Theorem eqb_refl : ∀ n : nat, true = (n =? n).
```

- **replace策略**：replace (t) with (u) 会将目标中表达式 t（的所有副本）替换为表达式 u， 并生成 t = u 作为附加的子目标，与assert类似功能

# Lists.v：使用结构化的数据

## 数值序对

- natprod：表示数值序对

```cpp
Notation "( x , y )" := (pair x y).
```

## 数值列表

“列表”描述：一个列表要么是空的，要么就是由一个数和另一个列表组成的序对

```cpp
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
```

```cpp
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity). //level表示优先级
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
```

```cpp
Fixpoint repeat (n count : nat) : natlist //它接受一个数字 n 和一个 count，返回一个长度为 count，每个元素都是 n 的列表
Fixpoint length (l:natlist) : nat //计算列表的长度
Fixpoint app (l1 l2 : natlist) : natlist app //函数用来把两个列表联接起来 (append)
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Definition hd (default:nat) (l:natlist) : nat // hd 函数返回列表的第一个元素（即“表头”）
Definition tl (l:natlist) : natlist // tl 函数返回列表除去第一个元素以外的部分（即“表尾”）
Fixpoint nonzeros (l:natlist) : natlist //把列表中的 0 去掉
Fixpoint oddmembers (l:natlist) : natlist //把列表中的奇数成员列出来
Definition countoddmembers (l:natlist) : nat //统计奇数个数
Fixpoint alternate (l1 l2 : natlist) : natlist //从两个列表中交替地取出元素并合并为一个列表， 就像把拉链“拉”起来一样
```

### **用列表实现口袋（Bag）**

```cpp
Fixpoint count (v:nat) (s:bag) : nat //计算 s 中 v 的个数
Definition sum : bag → bag → bag := app.
Definition add (v : nat) (s : bag) : bag := cons v s.
Definition member (v : nat) (s : bag) : bool //判断 v 是否在 s 中
Fixpoint remove_one (v:nat) (s:bag) : bag //删除 s 中的一个 v 元素
Fixpoint remove_all (v:nat) (s:bag) : bag //删除 s 中的所有 v 元素
Fixpoint subset (s1:bag) (s2:bag) : bool //判断 s1 是否为 s2 的子集（这里每个集合中元素是可以重复出现的）
```

## 有关列表的论证

对列表的分类讨论

```cpp
Theorem tl_length_pred : ∀ l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.
```

然而一般来说，许多关于列表的有趣定理都需要用到**归纳法**

我们想证明 P 对 '一切' 列表都成立，那么可以像这样推理：

- 首先，证明当 l 为 nil 时 P l 成立
- 然后，证明当 l 为 cons n l' 时 P l 成立，其中 n 是某个自然数，l' 是某个更小的列表，假设 P l' 成立.

之后如果证不出来，可以考虑 detruct n.

```cpp
Theorem app_assoc : ∀ l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
//反转列表
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil ⇒ nil
  | h :: t ⇒ rev t ++ [h]
  end.
Theorem app_length : ∀ l1 l2 : natlist, length (l1 ++ l2) = (length l1) + (length l2).
Theorem rev_length : ∀ l : natlist, length (rev l) = length l.
Theorem app_nil_r : ∀ l : natlist, l ++ [] = l.
Theorem rev_app_distr: ∀ l1 l2 : natlist, rev (l1 ++ l2) = rev l2 ++ rev l1.
Theorem rev_involutive : ∀ l : natlist, rev (rev l) = l.
Theorem app_assoc4 : ∀ l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Lemma nonzeros_app : ∀ l1 l2 : natlist, nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Fixpoint eqblist (l1 l2 : natlist) : bool //通过比较列表中的数字来判断是否相等
Theorem eqblist_refl : ∀ l:natlist, true = eqblist l l.
Theorem leb_n_Sn : ∀ n, n <=? (S n) = true.
Theorem remove_does_not_increase_count: ∀ (s : bag), (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
```

## Options可选类型

## 偏映射（Partial Maps）

定义一个新的归纳数据类型 id 来用作偏映射的“键”，本质上来说，id 只是一个数。但通过 Id 标签封装自然数来引入新的类型， 能让定义变得更加可读，同时也给了我们更多的灵活性

定义偏映射的类型：

```cpp
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
```

```cpp
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
//update 函数在部分映射中覆盖给定的键以取缔原值（如该键尚不存在， 则新建其记录）
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty ⇒ None
  | record y v d' ⇒ if eqb_id x y
                     then Some v
                     else find x d'
  end.
//find 函数按照给定的键搜索一个 partial_map。若该键无法找到，它就返回 None；若该键与 val 相关联，则返回 Some val。 若同一个键被映到多个值，find 就会返回它遇到的第一个值。
```

# Poly：多态与高阶函数

## 多态

布尔值列表

```cpp
Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).
```

避免为每种数据类型都定义不同的 constructor，定义“多态列表”数据类型：

```cpp
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
```

> list 是什么呢？

可以把 list 当作从 Type 类型到 Inductive 归纳定义的”函数“，或者说 list 是从 Type 类型到 Type 类型的函数。

元素类型为 X 的列表的集合

```cpp
Check list : Type → Type.
```

需要注意的是，现在调用 nil 和 cons 必须提供一个参数，就是它们要构造的列表的具体类型。例如：nil nat 构造的是 nat 类型的空列表

```cpp
Check (nil nat) : list nat.
```

cons nat 与此类似

以下示例构造了一个只包含自然数 3 的列表：

```cpp
Check (cons nat 3 (nil nat)) : list nat.
```

### 多态版列表处理函数

```cpp
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 ⇒ nil X
  | S count' ⇒ cons X x (repeat X x count')
  end.

```

Coq 自己推断类型标注、类型参数（用”_“代替）

### 隐式参数

Arguments 用于指令指定函数或构造子的名字并列出其参数名， 花括号中的任何参数都会被视作隐式参数。

```cpp
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.
```

## 多态序对（积）

- (x,y) 是一个'值'
- X×Y 是一个'类型'

```cpp
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X×Y)//接受两个列表，并将它们结合成一个序对的列表。 在其它函数式语言中，它通常被称作 zip
Fixpoint split {X Y : Type} (l : list (X×Y))
               : (list X) × (list Y)//是 combine 的右逆（right inverse）： 它接受一个序对的列表并返回一个列表的序对
```

## 过滤器

接受一个元素类型为 X 的列表和一个 X 的谓词（即一个从 X 到 bool 的函数），然后“过滤”此列表并返回一个新列表， 其中仅包含对该谓词返回 true 的元素

```cpp
//将 filter 应用到谓词 evenb 和一个数值列表 l 上，那么它就会返回一个只包含 l 中偶数的列表
Example test_filter1: filter evenb [1;2;3;4] = [2;4].
```

## 映射

```cpp
Fixpoint map {X Y: Type} (f:X→Y) (l:list X) : (list Y) :=
  match l with
  | [] ⇒ []
  | h :: t ⇒ (f h) :: (map f t)
  end.
Theorem map_rev : ∀ (X Y : Type) (f : X → Y) (l : list X), map f (rev l) = rev (map f l).
Fixpoint flat_map {X Y: Type} (f: X → list Y) (l: list X) : (list Y)//通过一个类型为 X → list Y 的函数 f 将 list X 映射到 list Y
flat_map (fun n ⇒ [n;n+1;n+2]) [1;5;10] = [1; 2; 3; 5; 6; 7; 10; 11; 12].
```

## 折叠fold

将给定的二元操作符 f 插入到给定列表的每一对元素之间

fold plus [1;2;3;4] 直观上的意思是 1+2+3+4，为了让它更精确，我们还需要一个“起始元素” 作为 f 初始的第二个输入。因此，例如 fold plus [1;2;3;4] 0 就会产生 1 + (2 + (3 + (4 + 0))).

```cpp
Fixpoint fold {X Y: Type} (f: X→Y→Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil ⇒ b
  | h :: t ⇒ f h (fold f t b)
  end.
```

# Tactics：更多基本策略

## apply策略：apply H.

- 待证目标与上下文中的前提或已证引理”刚好相同“时
- 如果被应用的语句是一个蕴含式，那么该蕴含式的前提就会被添加到待证子目标列表中
- 使用 apply 时，被应用的事实必须精确匹配
- apply I. 证明True

## symmetry.

可以交换证明目标中等式的左右两边

## apply with

```cpp
1 subgoal
n, m, o, p : nat
H : m = minustwo o
H0 : n + p = m
______________________________________(1/1)
n + p = minustwo o

执行 apply trans_eq with (m).

2 subgoals
n, m, o, p : nat
H : m = minustwo o
H0 : n + p = m
______________________________________(1/2)
n + p = m
______________________________________(2/2)
m = minustwo o
```

```cpp
Theorem S_injective : ∀ (n m : nat), S n = S m → n = m.

```

## apply in H.

- apply L in H 给了我们一种“正向推理”的方式：根据 X → Y 和一个匹配 X 的假设，它会产生一个匹配 Y 的假设
- apply L 是一种“反向推理”：它表示如果我们知道 X → Y 并且试图证明 Y， 那么证明 X 就足够了

```cpp
1 subgoal
n : nat
eq : (n =? 5) = true ->
     (S (S n) =? 7) = true
H : true = (S (S n) =? 7)
______________________________________(1/1)
true = (S (S n) =? 7)

执行 apply eq in H.

1 subgoal
n : nat
eq : (n =? 5) = true ->
     (S (S n) =? 7) = true
H : (S (S n) =? 7) = true
______________________________________(1/1)
true = (S (S n) =? 7)
```

## injection

可以让Coq利用构造子的单射性来产生所有它能从H所推出的等式，每一个这样的等式都作为假设被添加到上下文中

***可以想象成是对应拆开***

```cpp
1 subgoal
n, m, o : nat
H : [n; m] = [o; o]
______________________________________(1/1)
[n] = [m]

执行 injection H.

1 subgoal
n, m, o : nat
H : [n; m] = [o; o]
______________________________________(1/1)
m = o -> n = o -> [n] = [m]
```

## discriminate

对假设使用 discriminate，Coq会确认当前**正在证明的目标不可行**，并同时移除它，不再考虑。

因为它断言矛盾的前提会推出任何东西，甚至是假命题

```cpp
1 subgoal
n, m : nat
contra : false = true
______________________________________(1/1)
[n] = [m]

执行 discriminate contra.

No more subgoals.
```

```cpp
Theorem f_equal : ∀ (A B : Type) (f: A → B) (x y: A), x = y → f x = f y.
Theorem eq_implies_succ_equal : ∀ (n m : nat), n = m → S n = S m.
```

## f_equal:

当目标是一个归纳类型的构造函数等于同一个构造函数的时候，你可以用 f_equal. 转换成证明其中对应的部分是相同的

```cpp
v : valuation
e : arith
body, tbody : cmd
______________________________________(1/1)
Sequence (transform body) (While e (transform body)) =
Sequence tbody            (While e tbody)

执行 f_equal

v : valuation
e : arith
body, tbody : cmd
______________________________________(1/2)
transform body = tbody
______________________________________(2/2)
While e (transform body) = While e tbody
```

## 变换归纳假设

```cpp
Theorem double_injective: ∀ n m, double n = double m → n = m.
Theorem eqb_true : ∀ n m, n =? m = true → n = m.
```

在 intros 的时候要小心，有时候不能一起 intros m n. 这样之后 induction 会出现问题。

一般先 intros n. 然后再 induction n as [| n' IHn']. 然后在分支中 destruct m. 再进行后续证明。 

```cpp
1 subgoal
n, m, p : nat
H : n = m
H0 : (m =? p) = true
______________________________________(1/1)
(n =? p) = true

执行 apply eqb_true in H0.

1 subgoal
n, m, p : nat
H : n = m
H0 : m = p
______________________________________(1/1)
(n =? p) = true
```

## generalize dependent策略

选择性地从上下文中挑出几个变量并将它们放回证明目标的开始处

```cpp
Theorem nth_error_after_last: ∀ (n : nat) (X : Type) (l : list X), length l = n → nth_error l n = None.
```

## 展开定义unfold

```cpp
Theorem combine_split : ∀ X Y (l : list (X × Y)) l1 l2, split l = (l1, l2) → combine l1 l2 = l.
```

## 附加练习

```cpp
Theorem eqb_sym : ∀ (n m : nat), (n =? m) = (m =? n).
Theorem eqb_trans : ∀ n m p,
  n =? m = true →
  m =? p = true →
  n =? p = true.
Definition split_combine_statement : Prop :=
  forall (X Y:Type) (l1:list X) (l2:list Y), 
  length l1 = length l2 -> split (combine l1 l2) = (l1,l2).
```

# Logic：Coq中的逻辑系统

## 逻辑连接词

### 合取：

证明 → A ∧ B.

用 split. / apply and_intro. 策略

```cpp
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
```

证明 A ∧ B →

用 destruct 策略，如果当前证明上下文中存在形如 A ∧ B 的前提 H，那么 destruct H as [HA HB] 将会从上下文中移除 H 并增加 HA 和 HB 两个新的前提，前者断言 A 为真，而后者断言 B 为真。

```cpp
解构 H : n = 0 /\ m = 0
destruct H as [Hn Hm] eqn:HE.
或者在引入 H 的时候直接解构 intros n m [Hn Hm].
解构时也可以用下划线_丢弃不需要的合取分式 destruct HPQ as [HP _].
```

```cpp
Lemma and_example2 :
  ∀ n m : nat, n = 0 ∧ m = 0 → n + m = 0.
Lemma and_example3 :
  ∀ n m : nat, n + m = 0 → n × m = 0.
Lemma proj1 : ∀ P Q : Prop,
  P ∧ Q → P.
Lemma proj2 : ∀ P Q : Prop,
  P ∧ Q → Q.
//交换律
Theorem and_commut : ∀ P Q : Prop,
  P ∧ Q → Q ∧ P.
//结合律
Theorem and_assoc : ∀ P Q R : Prop,
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R.
```

### 析取：

证明 A ∨ B →

```cpp
Lemma eq_mult_0 :
  ∀ n m : nat, n = 0 ∨ m = 0 → n × m = 0.
Proof.
  (* Hn | Hm 会隐式地对 n = 0 ∨ m = 0 进行分类讨论 *)
  intros n m [Hn | Hm].
	Abort.
```

证明 → A ∨ B.

使用 left 和 right 策略来选取命题

```cpp
Lemma or_intro_l : ∀ A B : Prop, A → A ∨ B.

```

### 假命题与否定

如果 false 进入证明的上下文中，可以对它使用 destruct 来完成任何待证目标

```cpp
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P NP Q HP.
  apply NP in HP. (*重要，把假的寓于真的，证出假*)
  destruct HP.    (*证明 destruct false*)
Qed.
```

常使用

```cpp
unfold not.
Theorem contradiction_implies_anything : ∀ P Q : Prop,
  (P ∧ ¬P) → Q.
Theorem double_neg : ∀ P : Prop,
  P → ~~P.
Theorem contrapositive : ∀ (P Q : Prop),
  (P → Q) → (¬Q → ¬P).
Theorem not_both_true_and_false : ∀ P : Prop,
  ¬ (P ∧ ¬P).
```

如果你需要证明某个目标不可能时（例如当前的目标陈述为 **false = true**），请使用 **ex_falso_quodlibet/exfalso** 将该目标转换为 False。

### 逻辑等价: split. 策略

```cpp
Theorem iff_sym : ∀ P Q : Prop,
  (P ↔ Q) → (Q ↔ P).
Lemma not_true_iff_false : ∀ b,
  b ≠ true ↔ b = false.
Theorem or_distributes_over_and : ∀ P Q R : Prop,
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R).
```

证明的时候遇到

```cpp
1 subgoal
P, Q, R : Prop
______________________________________(1/1)
(P \/ Q) /\ (P \/ R) -> P \/ Q /\ R

执行 intros [[HP | HQ] [HP' | HR]].
```

## assumption

如果目标已经出现在假设里面了，你可以用 assumption. 来结束证明。

## 基本的iff等价关系命题

```cpp
Lemma mult_0 : ∀ n m, n × m = 0 ↔ n = 0 ∨ m = 0.
Lemma or_assoc :
  ∀ P Q R : Prop, P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R.
Lemma mult_0_3 :
  ∀ n m p, n × m × p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0.
```

存在量化

```cpp
1 subgoal
X : Type
P, Q : X -> Prop
x : X
HP : P x
______________________________________(1/1)
exists x0 : X, P x0

执行 exists x.

1 subgoal
X : Type
P, Q : X -> Prop
x : X
HP : P x
______________________________________(1/1)
P x
```

```cpp
1 subgoal
X : Type
P, Q : X -> Prop
HQ : exists x : X, Q x
______________________________________(1/1)
exists x : X, P x \/ Q x

执行 destruct HQ as [x HQQ].

1 subgoal
X : Type
P, Q : X -> Prop
x : X
HQQ : Q x
______________________________________(1/1)
exists x0 : X, P x0 \/ Q x0
```

# Indprop：归纳定义

### remember

在 Coq 中调用 remember e as x 策略会（1）替换所有表达式 e 为变量 x， （2）在当前上下文中添加一个等式 x = e。

# Imp：简单的指令式程序

## 算数和布尔表达式

抽象语法：

```cpp
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
```

## **try泛策略**

如果 T 是一个策略，那么 try T 是一个和 T 一样的策略，只是如果 T 失败的话，try T 就会'成功地'什么也不做（而非失败）

## **; 泛策略**

复合策略 T;T' 会先执行 T，然后在 T 生成的'每个子目标'中执行 T'

## **repeat 泛策略**

repeat 泛策略接受另一个测略并重复应用它直至失败。

## **omega 策略**

如果证明目标是由以下元素构成的式子：

- 数值常量、加法（+ 和 S）、减法（- 和 pred）以及常量乘法 （这就是 Presburger 算术的构成要素）
- 相等关系（= 和 ≠）和序（≤）
- 逻辑连结 ∧、∨、¬ 和 →

那么调用 omega 要么会解决该证明目标，要么就会失败，这意味着该目标为假

（注意本文件顶部 From Coq Require Import omega.Omega.。）

## 更多方便的技巧

- clear H：从上下文中删除前提 H。
- subst x：对于变量 x，在上下文中查找假设 x = e 或 e = x， 将整个上下文和当前目标中的所有 x 替换为 e 并清除该假设。
- subst：替换掉形如 x = e 或 e = x 的假设（其中 x 为变量）。

    '所有'

- rename... into...：更改证明上下文中前提的名字。例如， 如果上下文中包含名为 x 的变量，那么 rename x into y 就会将所有出现的 x 重命名为 y。
- assumption：尝试在上下文中查找完全匹配目标的前提 H。 如果找到了，那么其行为与 apply H 相同。
- contradiction：尝试在当前上下文中查找逻辑等价于 False 的前提 H。 如果找到了，就解决该目标。
- constructor：尝试在当前环境中的 Inductive 定义中查找可用于解决当前目标的构造子 c。如果找到了，那么其行为与 apply c 相同。

# 技巧

- Print+函数名.
- injection e as e1 e2.
    - before:

        e : (h1 :: t1, h2 :: t2) = (l1, l2)

    - after:

        e1 : h1 :: t1 = l1
        e2 : h2 :: t2 = l2

- inversion（对不正确的进行证明和化简）
    - injection
    - discriminate
- 遇事不决就 inversion/induction/destruct
- 遇到 ~(...)，首先 unfold not.
- Search：执行 Search foo 会让 Coq 显示所有涉及到 foo 的定理。例如，去掉下面的注释后， 你会看到一个我们证明过的所有关于 rev 的定理的列表：

    ```cpp
    (*  Search rev. *)
    ```