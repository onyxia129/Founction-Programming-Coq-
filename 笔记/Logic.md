



# 基本概念

### 1.prop

看作一种新的类型：命题



### 2./\ 和\/

`/\` ：交                        ` \/`：并



### 3.Ha : A

对A的证明



### 4.example

```
1 subgoal
A, B : Prop
HA : A
HB : B
______________________________________(1/1)
A /\ B
```



# 语法



## **split**

##### *形式* ：

 `split.`



##### *description* :

 把结论里面长成 `A /\ B` 的东西化简成 A B 两个subgoal

把`A<->B`这样的东西化简成两个subgoal `A->B`  和 `B->A`

##### *example：*

```
1 subgoal
A, B : Prop
HA : A
HB : B
______________________________________(1/1)
A /\ B
```

>split.

```
2 subgoals
A, B : Prop
HA : A
HB : B
______________________________________(1/2)
A
______________________________________(2/2)
B
```

---

```
1 subgoal
P : Prop
______________________________________(1/1)
P <-> P
```

> split.

```
2 subgoals
P : Prop
______________________________________(1/2)
P -> P
______________________________________(2/2)
P -> P
```



## **intros**进阶之带上destruct的例子

+ ### A/\B的形式

##### *形式* ：

1.`intors n m [Hn Hm].`

2.`intors n m [Hn _].`



##### *description* : 

intros 的同时destruct `A/\B` 为 `Hn:A Hn:B` 

2.缺省了原Hm的部分，那么Hm不会显示，一般是Hm在后面的证明用不到的情况。



##### *example：*

```
1 subgoal
______________________________________(1/1)
forall n m : nat, n = 0 /\ m = 0 -> n + m = 0
```

>  intros n m [Hn Hm].

```
1 subgoal
n, m : nat
Hn : n = 0
Hm : m = 0
______________________________________(1/1)
n + m = 0
```

---

```
1 subgoal
______________________________________(1/1)
forall P Q : Prop, P /\ Q -> Q
```

> intros P Q [_ HQ].

```
1 subgoal
P, Q : Prop
HQ : Q
______________________________________(1/1)
Q
```



---



+ ### A\/B的形式

##### *形式* ： 

1.`intors n m [Hn | Hm].`

2.`intors n m [Hn | _].`

##### *description* : 

intros 的同时destruct `A\/B` 为 `Hn:A Hn:B`

并且`Hn` 和`Hm`放在两个subgoal 里面

2.缺省同上

##### *example：*

```
1 subgoal
______________________________________(1/1)
forall n m : nat, n = 0 \/ m = 0 -> n * m = 0
```

>   intros n m [Hn | Hm].

```
2 subgoals
n, m : nat
Hn : n = 0
______________________________________(1/2)
n * m = 0
______________________________________(2/2)
n * m = 0
```



---



- ### 存在量词exists

##### *形式* ： 

`intros [x0 Hx0].`



##### *description* : 

x0是存在的那个x，Hx0 是代入x0后成立的式子



##### *example：*

```
1 subgoal
X : Type
P : X -> Prop
H : forall x : X, P x
______________________________________(1/1)
(exists x : X, P x -> False) -> False
```

> intros [x0 Hx0].

```
1 subgoal
X : Type
P : X -> Prop
H : forall x : X, P x
x0 : X
Hx0 : P x0 -> False
______________________________________(1/1)
False
```











## destruct

+ ### A/\B的形式

##### *形式* ：

1.`destruct n m [Hn Hm].`

2.`destruct n m [Hn _].`



##### *description* : 

destruct `A/\B` 为 `Hn:A Hn:B`

2.缺省了原Hm的部分，那么Hm不会显示，一般是Hm在后面的证明用不到的情况。



##### *example：*

```
1 subgoal
n, m : nat
H : n = 0 /\ m = 0
______________________________________(1/1)
n * m = 0
```

>destruct H as [Hn Hm].

```
1 subgoal
n, m : nat
Hn : n = 0
Hm : m = 0
______________________________________(1/1)
n * m = 0
```



---

##### *缺省：*

```
1 subgoal
P, Q : Prop
HPQ : P /\ Q
______________________________________(1/1)
P
```

> destruct HPQ as [HP _ ].

```
1 subgoal
P, Q : Prop
HP : P
______________________________________(1/1)
P
```



---



+ ### A\/B的形式

##### *形式* ：

1.`destruct n m [Hn | Hm].`

2.`destruct n m [Hn | _].`



##### *description* : 

destruct `A\/B` 为 `Hn:A Hn:B`

并且`Hn` 和`Hm`放在两个subgoal 里面

2.缺省了原Hm的部分，那么Hm不会显示，一般是Hm在后面的证明用不到的情况。



##### *example：*



---

+ ### False

##### *形式：*

```
A : False
```

`destruct A.` 



##### *description:* 

false 没有construct 也就是没有可以destruct的 所以就不用证明了
总结一下就是前提里有false 直接destruct就证明完成了



##### *example：*



---





- ### 存在量词exists

##### *形式* ： 

`destruct H as [x0 Hx0].`



##### *description* : 

H是本来的那句话

x0是存在的那个x，Hx0 是代入x0后成立的式子



##### *example：*

```
1 subgoal
X : Type
P, Q : X -> Prop
H : exists x : X, P x
______________________________________(1/1)
exists x : X, P x \/ Q x
```

> destruct H as [x1 Hx1].

```
1 subgoal
X : Type
P, Q : X -> Prop
x1 : X
Hx1 : P x1
______________________________________(1/1)
exists x : X, P x \/ Q x
```

























## left 和 right

##### *形式：*

`left.` `right.`



##### *description:* 

1.left ： 取结论里的 `A\/B` 左边

2.right ：取右边



##### *example：*

```
1 subgoal
A, B : Prop
HA : A
______________________________________(1/1)
A \/ B
```

> left.

```
1 subgoal
A, B : Prop
HA : A
______________________________________(1/1)
A
```





## intros 兼顾destruct的情况的概述

##### *形式：*

`intros a b [Ha Hb].` `intros a b [Ha|Hb].` 



##### *description:* 

`intros a b c.` 就是简单的intros

`intros a b [Ha Hb]` 就是把`c` destruct成`Ha` 和`Hb `

具体的看要intros的东西的格式，一般`[ ]`表示destruct 

至于`[ | ]`要不要竖杠线，目前已知的信息是`A\/B`的时候要，其他都不要。

具体不同情况还能套娃。

其实本质上是看`destruct H as 一个格式A` 

然后`intros` 本来写`H`的地方写 `格式A`



##### *example：*

```
1 subgoal
______________________________________(1/1)
forall P Q R : Prop, P <-> Q -> Q <-> R -> P <-> R
```

> intros P Q R [H1 H2] [H3 H4].

```
1 subgoal
P, Q, R : Prop
H1 : P -> Q
H2 : Q -> P
H3 : Q -> R
H4 : R -> Q
______________________________________(1/1)
P <-> R
```

+++

```
1 subgoal
P, Q, R : Prop
______________________________________(1/1)
P \/ Q \/ R -> (P \/ Q) \/ R
```

> intros [H | [H | H]].

```
3 subgoals
P, Q, R : Prop
H : P
______________________________________(1/3)
(P \/ Q) \/ R
______________________________________(2/3)
(P \/ Q) \/ R
______________________________________(3/3)
(P \/ Q) \/ R
```





## exists 存在量词

##### *形式：*

1.定义 : `exists o : nat, n = 2 + o`

2.使用 : `exists p0.`



##### *description:* 

定义里的`exists` 就和一般自然语言上说存在一个`x`，使得xxx怎么怎么样。

使用的话，是把`o = p0 `代入 式子 ，来化简。

##### *example：*

```
1 subgoal
n, m : nat
Hm : n = 4 + m
______________________________________(1/1)
exists o : nat, n = 2 + o
```

> exists (2 + m).

```
1 subgoal
n, m : nat
Hm : n = 4 + m
______________________________________(1/1)
n = 2 + (2 + m)
```



## True

结论里只有一个`True`的时候，用 `apply I`结束.

注意这个是命题的True 不是 bool的true 不一样的！



定义：

```
Inductive True : Prop :=  I : True
```



```
1 subgoal
______________________________________(1/1)
True
```

> apply I.

```
No more subgoals.
```





# 对参数应用定理

rewrite （定理名 参数1 参数2.。。）

apply 定理名 with 参数~



具体看logic这一章节



## exfalso





```
1 subgoal
H : forall P : Prop, P \/ ~ P
X : Type
P : X -> Prop
H0 : ~ (exists x : X, ~ P x)
x : X
NP : ~ P x
______________________________________(1/1)
P x
```

> exfalso.

```
1 subgoal
H : forall P : Prop, P \/ ~ P
X : Type
P : X -> Prop
H0 : ~ (exists x : X, ~ P x)
x : X
NP : ~ P x
______________________________________(1/1)
False
```

