# IndProp

## 概念理解

```
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).
```

上面是一个 ` a <= b `的 谓词逻辑的 递归 的 定义



#### 这其实是定义了两条规则:

第一句： $${\forall}$$ n ,满足n<=n     这是一个自己定义的定理
第二句： 已知H：$${\forall}$$ n ,满足n<=m   可以推出$\rightarrow$   $${\forall}$$ n，满足 n<= m+1

这两个自己定义的**<u>定理</u>**

由这两个定理，可以递归证明所有  ` a <= b `



#### 证明思路：

+ 正向：数学归纳法

  1. 当 t = a 时   

     $${\because}$$   $${\forall}$$ n ,满足n<=n   `定理一`

     $${\therefore}$$   a <= t

  ​    2. 假设 当 t = m 时， a <= t (m)

  ​			即定义的  已知H：$${\forall}$$ n ,满足n<=m     `H`

     3. 当 t = m + 1 时

         $${\because}$$   $${\forall}$$ n ,满足n<=m （已知）  可以推出$\rightarrow$   $${\forall}$$ n，满足 n<= m+1   `定理二`

         $${\therefore}$$   a <= t (m+1)

 综上，`a <= t `   t为>=a 的任意数字



+ 反向：

  由定理二可知：

  ​	要证明 `a <= b `，就要证明 `a<= b-1`，就要证明 `a<= b-2`

   	一直递减到 要证明 `a <=a`

  由定理一可知：

     `a <=a`显然成立

  所以`a <= b `得证





## destruct

用 destruct 来分解归纳定义的命题



## induction

和destruct一样



## remember

在destruct 或者 induction之后获得了一群不能证明的东西。

这是因为 destruct 或者induction 的对象是 `构造函数 表达式` 而不是 `构造函数 变量`

也就是我们想要的是 `ev x`  

但实际上有的是`ev S (S n)` 那么这个情况是不好destruct或者induction的

`remember (S (S n)) as k eqn:Hk.` 就可以把表达式换成变量了



## inversion

可以解决`构造函数 表达式`的问题

但是在某些情况下没有destruct和induction表现好