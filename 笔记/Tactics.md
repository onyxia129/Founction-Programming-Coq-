# Tactics

## intros

##### ***形式：***

`intros a b c d.`  引入自己要的

`intros.` 全部引入

##### ***Description：***

引入假设，每次引入会消耗一个`自由变量`（不再是for all 而是固定下来）或者一个$\rightarrow$前的式子

不再是for all 而是固定下来,这一点很重要，和后面讲更好的证明以及generalize dependent有关



## destruct

##### ***形式：***

`destruct n.`

`destruct n as [| n'] eqn:E.`

##### ***Description：***

分类讨论n的所有情况。分成若干个subgoal。

`[| n']` 是对n的每个可能值给个名字。`|`分割。  缺省就是不给名字(一般n=0或null的时候就不要名字的)

`eqn:E` 给每个sungoal里对应的等式取名字叫做`E`

***example:***

```
1 subgoal
n : nat
eq : double n = 0
______________________________________(1/1)
n = 0
```

> destruct n as [| n'] eqn:E.

```
2 subgoals
n : nat
E : n = 0
eq : double 0 = 0
______________________________________(1/2)
0 = 0
______________________________________(2/2)
S n' = 0
```

+ **subgoal1: n = 0**

```
1 subgoal
n : nat
E : n = 0
eq : double 0 = 0
______________________________________(1/1)
0 = 0
```

+ **subgoal2: n = S n'**

````
1 subgoal
n, n' : nat
E : n = S n'
eq : double (S n') = 0
______________________________________(1/1)
S n' = 0

````



## induction

##### ***形式：***

`induction n.`

`induction n as [| n' IHn'].`

##### ***Description：***

你可以 `induction` 一个归纳类型（*inductive type*），会产生和这个归纳类型的构造函数数量一样多的小目标。如果构造函数里面用到了这个归纳类型本身，那么在归纳的过程中会产生相应的归纳假设。

分subgoal部分和destruct一样

`IHn'` 是给归纳类型本身的名字



## apply

##### ***形式：***

`apply H.`

##### ***Description：***

1. ###### 已有假设条件H 需证明H  

   ![image-20201109165527943](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109165527943.png)

   > apply eq2

   就证明完了 直接`Qed.`

2. ###### 已有假设条件A$\rightarrow$B 需证明B 会化简成A

   ![image-20201109165858702](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109165858702.png)

   > apply eq2

   ![image-20201109165938381](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109165938381.png)

   

3. ###### 2的变体，参数不一致的情况，coq会自动检查，只要构造一样就行

![image-20201109170024907](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109170024907.png)

> apply eq2

![image-20201109170130858](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109170130858.png)

4. 已有假设条件A$\rightarrow$B 需证明A 会化简成B

   ```
   eq : (n =? 5) = true -> (S (S n) =? 7) = true
   H : (n =? 5) = true
   ```

   > apply eq in H.

   ```
   eq : (n =? 5) = true -> (S (S n) =? 7) = true
   H : (S (S n) =? 7) = true
   ```

   

##### ***形式：***

`apply A with B`

##### ***Description：***

A :已经证明好的一个可以用的定理

B:给A进行参数赋值，赋值本次证明里的参数

含义就是本次证明要调用A这个定理

##### ***example:***

已证明的传递性：`trans_eq`

```
Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.
```

需证明：

```
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
```

> intros a b c d e f eq1 eq2.

![image-20201109172148231](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109172148231.png)

>   apply ==trans_eq== with ==(m:=[c;d])==.

![image-20201109172353833](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109172353833.png)

#### P.S ：

这里写`apply trans_eq with ([c;d]).`也行。 Coq很聪明的



## transitivity

##### ***形式：***

`transitivity H` 

##### ***Description：***

Coq自带的传递性定理

A = B  转换成 A = H  H = B 

![image-20201109173351008](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109173351008.png)

> transitivity [c;d].

![image-20201109173427032](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109173427032.png)



## symmetry

##### ***形式：***

`symmetry`

##### ***Description：***

A=B 变成 B=A

![image-20201109170758368](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109170758368.png)

> symmetry.

![image-20201109170837493](C:\Users\ASUS\AppData\Roaming\Typora\typora-user-images\image-20201109170837493.png)



## injection

##### ***形式：***

`injection H as H1 H2...Hn.`

##### ***Description：***

官方的解释是：

we are asking Coq to generate all equations that it can infer from H using the injectivity of constructors. Each such equation is added as a hypothesis  into the context.

我的理解是：根据等式两边的形式（构造）做

1. 化简

```
1 subgoal
n, m : nat
H : S n = S m
______________________________________(1/1)
n = m
```

> injection H as Hnm.

```
1 subgoal
n, m : nat
Hnm : n = m
______________________________________(1/1)
n = m
```



2. 推导（等式两边一一对应，获得新的等式）

```
1 subgoal
n, m, o : nat
H : [n; m] = [o; o]
______________________________________(1/1)
[n] = [m]

```

>   injection H as H1 H2.

```
1 subgoal
n, m, o : nat
H1 : n = o
H2 : m = o
______________________________________(1/1)
[n] = [m]
```



## discriminate

##### ***形式：***

`discriminate H`

##### ***Description：***

H是一个显然错误的假设，那么在这个假设前提下推出什么都行，因为前提本身就不成立。

所以用可以`discriminate`来结束这一部分的证明

***example:***

```
1 subgoal
n, m : nat
contra : false = true
______________________________________(1/1)
[n] = [m]
```

> discriminate contra.

```
No more subgoals.
```



## f_equal.

##### ***形式：***

`f_equal.`

##### ***Description：***

$f(x)= f(y) \rightarrow\ x = y$

```
______________________________________(1/1)
S n = S m
```

> f_equal.

```
______________________________________(1/1)
n = m
```



## assert

##### ***形式：***

```
assert (H:definition).{prove it}
```

##### ***Description：***

定义一个本地的临时lemma

***example:***

```
1 subgoal
n, m : nat
H1 : S n = S m
______________________________________(1/1)
n = m
```

> assert (H2: n = pred (S n)). { reflexivity. }

```
1 subgoal
n, m : nat
H1 : S n = S m
H2 : n = Nat.pred (S n)
______________________________________(1/1)
n = m
```

#### P.S :

一般来讲还是拎出去写，好写而且清楚。



## rewrite

##### ***形式：***

`rewrite H.`         默认左往右

``rewrite -> H.``  从左往右重写

``rewrite <- H.``  从右往左重写

##### ***Description：***

重写 就是代入H。有方向，搞不清楚就两个方向都试一试



## simpl

##### ***形式：***

`simpl.`

##### ***Description：***

化简，功能很强大，遇事不决simpl一下



## reflexivity

##### ***形式：***

`reflexivity.`

##### ***Description：***

理解为把等式两边一样的东西去掉，结束证明的语句。



## unfold

##### ***形式：***

`unfold  函数名.`

##### ***Description：***

展开这个函数

***example:***

```
Definition square n := n * n.
```

```
______________________________________(1/1)
square (n * m) = square n * square m
```

>   unfold square.

```
______________________________________(1/1)
n * m * (n * m) = n * n * (m * m)
```



# inversion

##### ***形式：***

`inversion  H.`

`inversion E as [| n' E' Heq].` //这个和上面一样，就是自己给变量命名

##### ***Description：***

injection+discriminate+destruct  + 一些apply 

反正做好多事情。

也是分解，和destruct和induction同级别

它让 Coq 找出来要让 `H` 成立还有哪些事情要成立。

它有可能会添加新的假设，也可能会添加新的小目标。

也可能就证明完成了。

它也很强大。

***example:***

```
H : S n' * S m' = 0
______________________________________(1/1)
S n' = 0 \/ S m' = 0
```

>inversion H.

就证明完成了。

因为让H成立还需要S n' = 0 \/ S m' = 0这个结论成立，就正好证明完成了。



## generalize dependent

##### ***形式：***

`generalize dependent n.`

##### ***Description：***

intros的逆运算 把n变回自由变量（for all）

***example:***

```
1 subgoal
n, m : nat
______________________________________(1/1)
double n = double m -> n = m
```

>   generalize dependent n.

```
1 subgoal
m : nat
______________________________________(1/1)
forall n : nat, double n = double m -> n = m
```



# extensionality

***形式：***

`extensionality i.`

***Description：***

引入结论当中不能用intros引入的临时变量`x'`

***example:***

```
1 subgoal
A : Type
m : total_map A
x : string
v1, v2 : A
______________________________________(1/1)
(fun x' : string => if eqb_string x x' then v2 else if eqb_string x x' then v1 else m x') =
(fun x' : string => if eqb_string x x' then v2 else m x')
```

> extensionality i.

```
1 subgoal
A : Type
m : total_map A
x : string
v1, v2 : A
i : string
______________________________________(1/1)
(if eqb_string x i then v2 else if eqb_string x i then v1 else m i) =
(if eqb_string x i then v2 else m i)
```



## let

语法格式： let（fix）...A...in....B.....

  Definition plus1 (n:nat) : nat :=
    let b : nat := 1 in n+b.

compute plus1 3. 

A:可以是定义的一个函数
  这个函数的作用范围在B里面
B：也是一个函数

fix :A是递归的就加上

```
  Definition plus1 (n:nat) : nat :=
    let b : nat := 1 in n+b.
```

>Compute plus1 3. 

```
     = 4
     : nat
```







## replace

replace 策略允许你指定一个具体的要改写的子项和你想要将它改写成的项： 

replace (t) with (u) 会将目标中表达式 t（的所有副本）替换为表达式 u， 并生成 t = u 作为附加的子目标。

在简单的 rewrite 作用在目标错误的部分上时 这种做法通常很有用。

```
1 subgoal
n, m, p : nat
______________________________________(1/1)
m + p + n = m + (n + p)
```

> replace (n + p) with (p + n). 

```
2 subgoals
n, m, p : nat
______________________________________(1/2)
m + p + n = m + (p + n)
______________________________________(2/2)
p + n = n + p
```







## congruence

和discriminate一个意思，但是比它能力强，基本上就换这个用。









## Using Tactics on Hypotheses

##### ***形式：***

`apply... in H.`

`symmetry in H:`

`simpl...in H.`

`rewrite ... in H.`

`unfold... in H.`

##### ***Description：***

刚才介绍的一些tactics不仅可以对要证明的东西做，还可以对已有假设做，加个关键词in

***example:***

+ apply

```
eq : (n =? 5) = true -> (S (S n) =? 7) = true
H : (n =? 5) = true
```

> apply eq in H.

```
eq : (n =? 5) = true -> (S (S n) =? 7) = true
H : (S (S n) =? 7) = true
```



+ simpl

```
H : (S n =? S m) = b
```

> simpl in H.

``` 
H : (n =? m) = b
```



+ rewrite

```
H2 : y :: l = j
H0 : j = z :: l
```

> rewrite H0 in H2.

```
H2 : y :: l = z :: l
H0 : j = z :: l
```



## 对于有类似for all n m,多个参数的证明

不要一上来`intros n m.`

这么做等于两个参数都在变,并且在两个参数之间建立了一定的联系，但是实际需要证明的是任取n,m，也就是m，n之间不能有联系。



正确的做法是

1. `intros n`

2. `induction n .......`

3. 在2之后的subgoal里做`intros m`  和 `destruct m` 

***Description from book：***

```
we get stuck in the middle of the inductive case...
Theorem double_injective_FAILED : ∀ n m,
     double n = double m →
     n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
At this point, the induction hypothesis (IHn') does not give us n' = m' -- there is an extra S in the way -- so the goal is not provable.

Abort.
```



What went wrong?

The problem is that, at the point we invoke the induction hypothesis, we have already introduced m into the context -- intuitively, we have told Coq, "Let's consider some particular n and m..." and we now have to prove that, if `double n= double m` for *those particular* ` n  `and `m`, then `n = m`.

The next tactic, induction n says to Coq: We are going to show the goal by induction on` n`. That is, we are going to prove, for *all* `n`, that the proposition

+ P n = "if double n = double m, then n = m"

holds, by showing

+ P 0  = "if double O = double m then O = m"
+ P n → P (S n) = "if double n = double m then n = m" implies "if double (S n) = double m then S n = m"

If we look closely at the second statement, it is saying something rather strange: that, for a *particular* m, if we know

- "if double n = double m then n = m"

then we can prove

- "if double (S n) = double m then S n = m".

To see why this is strange, let's think of a particular (arbitrary, but fixed) m -- say, 5. The statement is then saying that, if we know

- Q = "if double n = 10 then n = 5"

then we can prove

- R = "if double (S n) = 10 then S n = 5".

But knowing Q doesn't give us any help at all with proving R! If we tried to prove R from Q, we would start with something like `"Suppose double (S n) = 10..." `but then we'd be stuck: knowing that double (S n) is 10 tells us nothing helpful about whether double n is 10 (indeed, it strongly suggests that double n is *not* 10!!), so Q is useless.

Trying to carry out this proof by induction on n when m is already in the context doesn't work because we are then trying to prove a statement involving *every* n but just a *single* `m`.



# Using destruct on Compound Expressions

##### ***形式：***

`destruct  一个式子`

##### ***Description：***

和普通的destruct一样，就是扩展了对象，一般和 `unfold`一起用

***example:***

```
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.
```

```
1 subgoal
n : nat
______________________________________(1/1)
sillyfun n = false
```

> unfold sillyfun.

```
1 subgoal
n : nat
______________________________________(1/1)
(if n =? 3 then false else if n =? 5 then false else false) = false
```

> destruct (n =? 3) eqn:E1.

```
2 subgoals
n : nat
E1 : (n =? 3) = true
______________________________________(1/2)  //subgoal1:  n =? 3 = true 
false = false
______________________________________(2/2)  //subgoal2:  n =? 3 = false 
(if n =? 5 then false else false) = false
```



## Review

+ `intros`: move hypotheses/variables from goal to context
+ `reflexivity`: finish the proof (when the goal looks like e = e)
+ `apply`: prove goal using a hypothesis, lemma, or constructor
+ `apply... in H`: apply a hypothesis, lemma, or constructor to a hypothesis in the context (forward reasoning)
+ `apply... with...`: explicitly specify values for variables that cannot be determined by pattern matching
+ `simpl`: simplify computations in the goal
+ `simpl`: in H: ... or a hypothesis
+ `rewrite`: use an equality hypothesis (or lemma) to rewrite the goal
+ `rewrite ... in H`: ... or a hypothesis
+ `symmetry`: changes a goal of the form t=u into u=t
+ `symmetry in H`: changes a hypothesis of the form t=u into u=t
+ `transitivity y`: prove a goal x=z by proving two new subgoals, x=y and y=z
+ `unfold`: replace a defined constant by its right-hand side in the goal
+ `unfold... in H`: ... or a hypothesis
+ `destruct... as...`: case analysis on values of inductively defined types
+ `destruct... eqn:...`: specify the name of an equation to be added to the context, recording the result of the case analysis
+ `induction... as...`: induction on values of inductively defined types
+ `injection`: reason by injectivity on equalities between values of inductively defined types
+ `discriminate:` reason by disjointness of constructors on equalities between values of inductively defined types
+ `assert (H: e) (or assert (e) as H)`: introduce a "local lemma" e and call it H
+ `generalize dependent x`: move the variable x (and anything else that depends on it) from the context back to an explicit hypothesis in the goal formula
+ `f_equal`: change a goal of the form f x = f y into x = y