+++
title = "[TaPL] 18 Imperative Objects"
author = ["roife"]
date = 2024-07-23
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论", "程序语义", "subtyping"]
draft = false
+++

本章通过前面介绍的特性建模面向对象编程。


## Object-Oriented Programming {#object-oriented-programming}

OOP 是一个宽泛的概念，在不同的语言中有不同的建模。这里先介绍这些语言中的一些共性：

-   **Multiple representation**：在一个对象上执行操作时，由对象自己决定如何执行。实现了相同接口（**interface**）的对象可以有不同的实现。这些实现称为方法（**methods**）。在对象上执行操作称为 **method invocation** 或 **sending message**，这会在对象的运行时方法表中查找对应的操作，这个过程称为 **dynamic dispatch**。而 ADT 的是由一组值和一个唯一的 implementation 组成的。
-   **Encapsulation**：对象的内部状态对外部是不可见的，只有对象自己的方法可以访问。这使得对象内部的更改只影响对象自己，这种限制提高了大型程序的可维护性。ADT 也有类似的特性。
    -   在部分语言（如 smalltalk）中会强制封装，对象内部的字段都是私有的，而所有方法都是公有的。Java 和 C++ 中则是通过关键字来实现封装，允许将字段或方法使用不同的访问权限。
    -   也有些语言（例如 Cecil 中）不会进行封装，使用 **multi-methods** 来实现面向对象机制。**Multi-methods** 将对象的状态和方法分开，使用 type-tags 在重载的方法中选择合适的方案。尽管它看起来和本章讨论的机制类似，但是它们在原理上有根本的不同。
-   **Subtyping**：对象的类型（即 **interface**）是由操作的名字和操作的类型组成的集合。对象的内部表示不出现在类型中，因为内部表示不影响对象能够执行的操作集合。Interfaces 通常满足 subtyping 关系：如果一个对象满足 interface \\(I\\)，那么它也满足 \\(I\\) 的子集 \\(I'\\)，其中 \\(I'\\) 是 \\(I\\) 的子集。因此对象的 subtyping 关系类似于 record 的 subtyping 关系。这种 subtyping 关系使得用户可以用统一的方式操作不同类型的对象。
-   **Inheritance**：共享 interface 的对象通常也会共享行为，因此通常会希望只实现一次共享的部分。大多数面向对象语言通过 **classes**（即 **objects** 实现的 template）以及 **subclassing** 机制来实现新方法添加和对旧方法选择性的重写。也有一些面向对象语言通过 **delegation** 机制来实现继承。
-   **Open recursion**：大多数实现了 **classes** 和 **objects** 的语言都提供了 **self** 或 **this** 关键字，用于在方法中调用自己的其他方法。**self** 的特点在于它是 **late bound** 的，即允许类中的方法调用其子类的方法。


### Multi-methods {#multi-methods}

> 参考 _Object-Oriented Multi-Methods in Cecil_


#### Single Dispatching {#single-dispatching}

在大多数面向对象语言中，消息会被发送到一个特殊的 receiver，并由 receiver 的运行时类型决定调用的方法。消息的其他参数不参与到方法查找中。这种机制称为 **single dispatching**。

Single dispatching 强调了方法的首参数比其他参数更加**重要**，并由首参数决定方法的分发，这导致了非对称性，对于一些操作非常不自然，例如：

-   对象的一些二元操作或多元操作是可交换的，例如加法、乘法等。
-   对象的一些操作没有主次之分，例如 `pairDo(c1, c2, block)` 会在两个集合中并行遍历并执行 `block`，两个集合的地位是平等的，但是程序员必须偏向其中一个集合。
-   对象的多个参数共同决定了执行方法，例如 `drawLine(shape, device)` 如果不同的设备上绘制不同的图形，那么会选择完全不同的方法，二者共同决定了方法的执行。


#### Double Dispatching {#double-dispatching}

在只允许 single-dispatching 的语言中，解决非对称性的一个方案是 **double dispatching**。Double-dispatching 将一个方法分成了两个方法：一个用于启动 double-dispatching，另一个用于执行不同类型上对应的操作（在 Java 中遇到这种情况也会用 `instanceof` 来实现对不同的 `rhs` 执行不同操作，相当于人为分发代码，本质上和 double-dispatching 没有区别）。

例如对于一对二维点的比较操作：

```ocaml
(** Point *)
self = rhs {
    return self.x == rhs.x && self.y == rhs.y;
}
```

但是这里的 `self` 和 `rhs` 是对称的，需要保证 `rhs` 也是一个点：

```ocaml
(** Point *)
self = rhs {
    return rhs.equalPoint(self);
}
self.equalPoint(rhs) {
    return self.x == rhs.x && self.y == rhs.y;
}

(** Object *)
self.equalPoint(rhs) {
    return false;
}
```

显然这种做法非常麻烦，程序员需要定义多余的代码来处理无意义的集合。


#### Multi-Methods {#multi-methods}

支持 **multi-methods** 的语言允许方法的调用不仅仅依赖于 receiver，还依赖于其他参数，知名的语言包括 CLOS、Cecil 等。

例如前面关于 `equal` 的例子：

```ocaml
(** equal 的默认实现（不对任何参数进行分派）返回 false： *)
   x = y { return false; }

(** 对于 Point 类型的参数，equal 会对参数进行分派： *)
--（v@obj 意味着对参数 v 进行分派，并且仅匹配与 obj 相等或继承自 obj 的实际参数）：
   p1@Point = p2@Point { return p1.x = p2.x && p1.y = p2.y; }
```


## Objects {#objects}

通常情况下可以把对象（**object**）看成一种数据结构，封装了一组内部状态，外部可以通过方法进行访问。状态组织成多个可变字段（fields），在方法间共享，但是对程序的其余部分不可见。

本章将以一个支持递增和返回当前值的对象为例。这个对象有两个方法：\\(\operatorname{\mathtt{get}}\\) 和 \\(\operatorname{\mathtt{inc}}\\)，分别用于获取当前值和递增当前值，并通过 abstractions 来实现延迟求值：

```ocaml
c = let x = ref 1 in
       { get = λ_:Unit. !x,
         inc = λ_:Unit. x := succ(!x) };
(** c : { get: Unit -> Nat, inc: Unit -> Unit } *)

c.inc unit; c.inc unit; c.get unit;
(** 3: Nat *)
```

可以利用别名来简化这个类型：

\\[\operatorname{\mathtt{Counter}} = \\{ \operatorname{\mathtt{get}}: \operatorname{\mathtt{Unit}} \rightarrow \operatorname{\mathtt{Nat}}, \operatorname{\mathtt{inc}}: \operatorname{\mathtt{Unit}} \rightarrow \operatorname{\mathtt{Unit}} \\}\\]

此外由于存在封装，因此这里的状态（\\( x \\)）不会对外暴露，只能在词法作用域中被访问。

<div class="note">

对象可以通过 **object generator**来生成。**Object generator** 是一个函数，接受一些参数，返回一个对象。

```ocaml
newCounter =
  λ_:Unit. let x = ref 1 in
              { get = λ_:Unit. !x,
                inc = λ_:Unit. x := succ(!x) };
(** newCounter : Unit -> Counter *)
```

</div>


## Subtyping {#subtyping}

OOP 受到欢迎的原因之一是它允许一段代码处理许多不同形状的对象。

例如定义 `ResetCounter`：

```ocaml
ResetCounter = { get: Unit → Nat, inc: Unit → Unit, reset: Unit → Unit };
```

那么有 \\(\operatorname{\mathtt{ResetCounter}} <: \operatorname{\mathtt{Counter}}\\)。因此所有能够处理 `Counter` 的函数都能处理 `ResetCounter`。


## Instance Variables {#instance-variables}

一个对象可能会有多个实例变量，因此最好将他们打包成一个 record type 一起操作：

```ocaml
c = let r = {x = ref 1} in
      { get = λ_:Unit. !(r.x),
        inc = λ_:Unit. r.x := succ(!(r.x)) };
```

由实例变量自成的 record 称为对象的 **representation type**：

\\[
\operatorname{\mathtt{CounterRep}} = \\{ x: \operatorname{\mathtt{Ref}}\ \operatorname{\mathtt{Nat}} \\}
\\]


## Classes {#classes}

上面的 `ResetCounter` 和 `Counter` 的定义几乎相同，只是多了一个 `reset`。为了减少重复，最好用一个东西描述通用功能，然后允许对其进行扩展。这个机制称为类（**classes**）。

Real-world PL 的类包括复杂的功能，包括 `self`、`super`、visibility、static 等。这是因为在这些语言中，类是唯一的结构化组织结构，因此需要包含所有的功能。而 OCaml 等语言则分开了 classes 和 modules。这里只关注类的基础功能：通过 inheritance 实现代码重用，以及对 `self` 的绑定。

类的最原始的形式是持有一组方法的数据结构，这些方法可以被实例化（**instantiated**）并产生一个新的对象，或者被扩展（**extended**）并产生一个新的类。


### Adding Methods {#adding-methods}

为了能扩展 classes 的 fields 和 methods，应该将 `newCounter` 拆分成两部分：一部分定义 method bodies，方法能够通过 representation 访问字段组成的的 record；另一部分生成一个 record 作为 fields，并将其传递给 method bodies 并生成 `counter`。

```ocaml
counterClass =
  λr:CounterRep.
    { get = λ_:Unit. !(r.x),
      inc = λ_:Unit. r.x := succ(!(r.x)) };
(** counterClass : CounterRep → Counter *)
```

```ocaml
newCounter =
  λ_:Unit. let r = {x=ref 1} in
             counterClass r;
(** newCounter : Unit → Counter *)
```

这样就可以对类进行扩展，通过 `Counter` 定义 `resetCounter`：

```ocaml
resetCounterClass =
  λr:CounterRep.
    let super = counterClass r in
      { get   = super.get,
        inc   = super.inc,
        reset = λ_:Unit. r.x := 1 };
(** resetCounterClass : CounterRep → ResetCounter *)
```

```ocaml
newResetCounter =
  λ_:Unit. let r = {x=ref 1} in resetCounterClass r;
(** newResetCounter : Unit → ResetCounter *)
```

`ResetCounterClass` 首先使用 `counterClass` 父对象并绑定到 `super`。然后，它通过从 `super` 复制 `get` 和 `inc`，并为 `reset` 字段提供新函数来构建新对象。由于 `super` 是基于 `r` 构建的，所以这三个方法共享相同的实例变量。

这里需要强调的是 classes 是 values 而不是 types，因为它们是函数。而在 Java 等语言中，classes 既是 types 也可以作为数据结构。


### Adding Instance Variables {#adding-instance-variables}

通常情况下，扩展类是不仅会添加方法，还会添加实例变量。

假设这里有一个 `BackupCounter` 类，需要记录一个历史值，后续 `reset` 时会将当前值设置为历史值：

```ocaml
BackupCounter = { get: Unit → Nat, inc: Unit → Unit,
                  reset: Unit → Unit, backup: Unit → Unit };
```

```ocaml
BackupCounterRep = { x: Ref Nat, b: Ref Nat };
```

类似地让 `BackupCounterClass` 继承自 `ResetCounterClass`：

```ocaml
backupCounterClass =
  λr:BackupCounterRep.
    let super = resetCounterClass r in
      { get    = super.get,
        inc    = super.inc,
        reset = λ_:Unit. r.x := !(r.b),
        backup = λ_:Unit. r.b := !(r.x) };
(** backupCounterClass : BackupCounterRep → BackupCounter *)
```

这里需要注意两点：

-   子对象继承并覆写了父对象的方法 `reset`
-   由于 \\(\operatorname{\mathtt{BackupCounterRep} <: \operatorname{\mathtt{CounterRep}}}\\)，因此可以使用 \\(\operatorname{\mathtt{BackupCounterRep}}\\) 生成 \\(\operatorname{\mathtt{ResetCounter}}\\)。

由于在定义新类时绑定了 `super`，因此在覆写方法时可以使用 `super.inc` 来调用父类的方法。


## Self {#self}

为类添加 `self` 可以让类的方法调用自己的其他方法。但是目前我们把方法保存在 records 中，如果一个方法能访问到对象的其他方法，那么这就构成了一个递归。

例如这里添加一个 `SetCounter` 类，让 `inc` 调用 `self.set` 来实现递增：

```ocaml
SetCounter = { get: Unit → Nat, set: Nat → Unit, inc: Unit → Unit };
```

```ocaml
setCounterClass =
  λr:CounterRep.
    fix (
      λself: SetCounter.
         { get = λ_:Unit. !(r.x),
           set = λi:Nat. r.x := i,
           inc = λ_:Unit. self.set (succ (self.get unit))});
(** setCounterClass : CounterRep → SetCounter *)
```

```ocaml
newSetCounter =
  λ_:Unit.
    let r = {x=ref 1} in
      setCounterClass r;
(** newSetCounter : Unit → SetCounter *)
```

这个类没有父类，因此不需要 `super`。

下面以 `SetCounter` 为例，展示 `self` 的 reduction 过程：

\begin{align\*}
o&: \operatorname{\mathtt{setCouter}} = \operatorname{\mathtt{newSetCouter}}\ \operatorname{\mathtt{unit}} \\\\
& = \operatorname{\mathtt{fix}}\ (\lambda \operatorname{\mathtt{self}}.\ \\{\operatorname{\mathtt{get}};\ \operatorname{\mathtt{set}};\ \operatorname{\mathtt{inc}}\\}) \\\\
& \rightarrow (\lambda \operatorname{\mathtt{self}}.\ \\{\operatorname{\mathtt{get}};\ \operatorname{\mathtt{set}};\ \operatorname{\mathtt{inc}}\\})\ (\operatorname{\mathtt{fix}}\ (\lambda \operatorname{\mathtt{self}}.\ \\{\operatorname{\mathtt{get}};\ \operatorname{\mathtt{set}};\ \operatorname{\mathtt{inc}}\\})) \\\\
& \rightarrow \\{\operatorname{\mathtt{get}};\ \operatorname{\mathtt{set}};\ \operatorname{\mathtt{inc}} = \lambda\ \\\_.\ S.\operatorname{\mathtt{set}}\ (\operatorname{\mathtt{succ}}\ S.\operatorname{\mathtt{get}}\ \operatorname{\mathtt{unit}}))\\} \\\\
& \quad \text{where}\ S = \operatorname{\mathtt{fix}}\ (\lambda \operatorname{\mathtt{self}}.\ \\{\operatorname{\mathtt{get}};\ \operatorname{\mathtt{set}};\ \operatorname{\mathtt{inc}}\\}) \\\\
& \quad \quad \rightarrow \\{\operatorname{\mathtt{get}};\ \operatorname{\mathtt{set}};\ \operatorname{\mathtt{inc}} = \lambda\ \\\_.\ S.\operatorname{\mathtt{set}}\ (\operatorname{\mathtt{succ}}\ S.\operatorname{\mathtt{get}}\ \operatorname{\mathtt{unit}}))\\} \\\\
\\\\
o&.\operatorname{\mathtt{inc}}\ \operatorname{\mathtt{unit}} \\\\
\rightarrow &\ S.\operatorname{\mathtt{set}}\ (\operatorname{\mathtt{succ}}\ S.\operatorname{\mathtt{get}}\ \operatorname{\mathtt{unit}}) \\\\
= &\ o.\operatorname{\mathtt{set}}\ (\operatorname{\mathtt{succ}}\ o.\operatorname{\mathtt{get}}\ \operatorname{\mathtt{unit}}) \\\\
\end{align\*}

可以看到最后对 `self` 的调用都转换成了对当前对象的其他方法的调用。

因此一个包含递归方法的对象是一个返回 records 的方法的不动点，设函数 \\( P = \lambda \operatorname{\mathtt{self}}. \\{m₁ = e₂, \dots, mₙ = eₙ\\} \\)，则它构建的对象为 \\( \operatorname{\mathtt{fix}}\ P \\)。


## Open recursion {#open-recursion}

大多数面向对象语言支持 open recursion，即父类中的方法可以通过 `self` 调用自己的子类的方法。例如子类覆写了父类的某个方法 `f`，那么父类中的方法调用 `self.f` 时会自动分发到子类的 `f`。

为了实现这个行为，首先我们要将 `fix` 移动到创建对象的地方：

```ocaml
setCounterClass =
  λr:CounterRep.
    λself: SetCounter.
      { get = λ_:Unit. !(r.x),
        set = λi:Nat. r.x := i,
        inc = λ_:Unit. self.set (succ(self.get unit)) };
(** setCounterClass : CounterRep → SetCounter → SetCounter *)
```

```ocaml
newSetCounter =
  λ_:Unit.
    let r = {x=ref 1} in
      fix (setCounterClass r);
(** newSetCounter : Unit → SetCounter *)
```

移动之后 `setCounterClass` 的签名发生改变：不仅传入了当前的实例变量，还传入了一个 `self`-object。二者都会在对象实例化的时候被提供。这里 `self` 的定义不再是“当前类”，而是“当前对象实例化的类”（有可能是当前类的子类）。

这里以 `instrCounter` 为例，它能够在 `set` 时记录当前的次数：

```ocaml
InstrCounter = { get: Unit → Nat, set: Nat → Unit,
                 inc: Unit → Unit, accesses: Unit → Nat };
```

\\[\operatorname{\mathtt{instrCounterRep}} = \\{ x: \operatorname{\mathtt{Ref}}\ \operatorname{\mathtt{Nat}},\ a: \operatorname{\mathtt{Ref}}\ \operatorname{\mathtt{Nat}} \\}\\]

```ocaml
instrCounterClass =
  λr:InstrCounterRep.
    λself: InstrCounter.
      let super = setCounterClass r self in
        { get = super.get,
          set = λi:Nat. (r.a := succ(!(r.a)); super.set i),
          inc = super.inc,
          accesses = λ_:Unit. !(r.a) };
(** instrCounterClass : InstrCounterRep → InstrCounter → InstrCounter *)
```

此处 `instrCounter` 重载了 `set` 方法，但是 `inc` 仍使用父类的方法。当调用 `super.inc` 时，父类的 `inc` 会调用 `self.set`，这里的 `self` 来自于子类，因此会分发到子类的 `set` 方法。

当子类调用 \\(\operatorname{\mathtt{super.set}}\\)，即当父类调用 \\(\operatorname{\mathtt{self}}.\operatorname{\mathtt{set}}\\)（此处 \\(\operatorname{\mathtt{self}}\\) 来自 \\(\operatorname{\mathtt{newinstrCounter}}\\) 传入）时，会展开成 \\((\operatorname{\mathtt{fix}}\ (\operatorname{\mathtt{instrCounterClass}}\ r)).\operatorname{\mathtt{set}}\\)，即 \\((\lambda \operatorname{\mathtt{self}}.\ \langle \operatorname{\mathrm{instrMethods}} \rangle).\operatorname{\mathtt{set}}\\)。


### Evaluation Order Problem {#evaluation-order-problem}

然而上面定义的 `instrCounterClass` 还有一个问题求值顺序的问题，导致无法构建实例：

\begin{align\*}
  & \operatorname{\mathtt{newinstrCounter}}\ \operatorname{\mathtt{unit}} \\\\
\rightarrow & \operatorname{\mathtt{let}}\ r =\ \\{x =\operatorname{\mathtt{ref}}\ 1,\ a =\operatorname{\mathtt{ref}}\ 0\\} \ \operatorname{\mathtt{in}}\ \operatorname{\mathtt{fix}}\ (\operatorname{\mathtt{instrCounterClass}}\ r) \\\\
\rightarrow & \operatorname{\mathtt{fix}}\ (\operatorname{\mathtt{instrCounterClass}}\ \langle \operatorname{\mathrm{vars}} \rangle) \\\\
= & \operatorname{\mathtt{fix}}\ (\lambda \operatorname{\mathtt{self}}: \operatorname{\mathtt{instrCounter}}.\\\\
& \qquad \qquad \operatorname{\mathtt{let}}\ \operatorname{\mathtt{super}} =\ \operatorname{\mathtt{setCounterClass}}\ \langle \operatorname{\mathrm{vars}} \rangle\ \operatorname{\mathtt{self}} \ \operatorname{\mathtt{in}}\ \langle \operatorname{\mathrm{methods}} \rangle) \\\\
\rightarrow & \operatorname{\mathtt{let}}\ \operatorname{\mathtt{super}} = \operatorname{\mathtt{SetCounterClass}}\ \langle \operatorname{\mathrm{vars}} \rangle\ (\operatorname{\mathtt{fix}}\ \langle f \rangle) \ \operatorname{\mathtt{in}}\ \langle \operatorname{\mathrm{methods}} \rangle & (\text{Def of $\operatorname{\mathtt{fix}}$}) \\\\
& \qquad \qquad \text{where $f = \operatorname{\mathtt{fix}}\ (\lambda \operatorname{\mathtt{self}}.\ \dots)$}\\\\
\rightarrow & \operatorname{\mathtt{let}}\ \operatorname{\mathtt{super}} = (\lambda \operatorname{\mathtt{self}}: \operatorname{\mathtt{SetCounter}}.\ \langle \operatorname{\mathrm{sup\\\_methods}} \rangle)\ (\operatorname{\mathtt{fix}}\ \langle f \rangle) \ \operatorname{\mathtt{in}}\ \langle \operatorname{\mathrm{methods}} \rangle \\\\
\rightarrow & \operatorname{\mathtt{let}}\ \operatorname{\mathtt{super}} = (\lambda \operatorname{\mathtt{self}}: \operatorname{\mathtt{SetCounter}}.\ \langle \operatorname{\mathrm{sup\\\_methods}} \rangle)\ \\\\
& \qquad \qquad \qquad \quad (\operatorname{\mathtt{let}}\ \operatorname{\mathtt{super}} = \operatorname{\mathtt{setCounterClass}}\ \langle \operatorname{\mathrm{vars}} \rangle\ (\operatorname{\mathtt{fix}}\ \langle f \rangle) \operatorname{\mathtt{in}}\ \langle \operatorname{\mathrm{methods}} \rangle) \\\\
& \qquad \operatorname{\mathtt{in}}\ \langle \operatorname{\mathrm{methods}} \rangle & (\text{$\operatorname{\mathrm{E-App}}$}) \\\\
\rightarrow & \operatorname{\mathtt{let}}\ \operatorname{\mathtt{super}} = (\lambda \operatorname{\mathtt{self}}: \operatorname{\mathtt{SetCounter}}.\ \langle \operatorname{\mathrm{sup\\\_methods}} \rangle)\ \\\\
& \qquad \qquad \qquad \quad (\operatorname{\mathtt{let}}\ \operatorname{\mathtt{super}} = (\lambda \operatorname{\mathtt{self}}: \operatorname{\mathtt{SetCounter}}.\ \langle \operatorname{\mathrm{sup\\\_methods}} \rangle)\ (\operatorname{\mathtt{fix}}\ \langle f \rangle)\\\\
& \qquad \qquad \qquad \qquad \quad \operatorname{\mathtt{in}}\ \langle \operatorname{\mathrm{methods}} \rangle) \\\\
& \qquad \operatorname{\mathtt{in}}\ \langle \operatorname{\mathrm{methods}} \rangle & (\text{$\operatorname{\mathrm{E-Abs}}$}) \\\\
\end{align\*}

可以看到最后一个结果中，出现了一个与外部 application 相同的内部 application，根据 evaluation 的规则，这里需要继续展开 \\(\operatorname{\mathtt{fix}}\ \langle f \rangle\\)，这样会导致无限展开。

这个问题的根源在于 \\(\operatorname{\mathtt{fix}}\ \langle f \rangle\\) 的求值是 eager 的，导致当它出现在 application 中作为参数时会被立即展开。为了避免这种情况，在使用 \\(\operatorname{\mathtt{fix}}\ (\lambda x. t)\\) 时应当让 \\(t\\) 中对 \\(x\\) 的引用是 lazy 的。

对于这个问题有几种解决方案：

-   将 `instrCounterClass` 中对 `self` 的引用用 lambda abstraction 包裹一层，实现 lazy evaluation。
-   使用一些 low-level 的语义建模类，例如使用 method table 而不是 `fix` 来实现（下一个节会使用这个方法）
-   不再用 STLC 建模 objects 和 classes，而直接将其视作 primitives（下一个章会使用这个方法）

这里先采用第一种方案，做法是使用 \\(\lambda\ \\\_: \operatorname{\mathtt{Unit}}. t\\) 来包裹 `self`：

```ocaml
setCounterClass =
  λr: CounterState.
    λself: Unit → SetCounter.
      λ_: Unit.
        { get = λ_: Unit. !(r.x),
          set = λi: Nat.  r.x := i,
          int = λ_: Unit. (self unit).set (succ ((self unit).get unit)) };
(** setCounterClass : CounterRep → (Unit → SetCounter) → Unit → SetCounter *)
```

```ocaml
newSetCounter =
  λ_:Unit.
    let r = {x=ref 1} in
      fix (setCounterClass r) unit;
(** newSetCounter : Unit → SetCounter *)
```

缺点就是这里使用 `self` 都要多写一次 \\(\operatorname{\mathtt{self}}\ \operatorname{\mathtt{unit}}\\)，并且使用所有函数（例如 \\(get\\)）都要传入一个 \\(\operatorname{\mathtt{unit}}\\) 触发执行。

\\[\operatorname{\mathtt{ic.set}}\ 5;\ \operatorname{\mathtt{ic.accesses}}\ \operatorname{\mathtt{unit}}\\]


## A More Efficient Implementation {#a-more-efficient-implementation}

上面的实现中每次使用 `self` 都要计算一次 `(self unit)`，计算开销很大。为了避免这个问题，可以直接将 objects 的 methods 包装在 `Ref` 中：

```ocaml
setCounterClass =
  λr:CounterRep. λself: Ref SetCounter.
    { get = λ_:Unit. !(r.x),
      set = λi:Nat. r.x := i,
      inc = λ_:Unit. (!self).set (succ ((!self).get unit))};
(** setCounterClass : CounterRep → (Ref SetCounter) → SetCounter *)
```

使用时先为类方法分配一个 dummy 方法集合，然后在 dummy 集合上构造真实的方法覆盖掉（back-patch），最后返回真实的方法集合：

```ocaml
dummySetCounter =
  { get = λ_:Unit. 0,
    set = λi:Nat. unit,
    inc = λ_:Unit. unit };
(** dummySetCounter : SetCounter *)
```

```ocaml
newSetCounter =
  λ_:Unit.
    let r = {x=ref 1} in
      let cAux = ref dummySetCounter in
        (cAux := (setCounterClass r cAux); !cAux);
(** newSetCounter : Unit → SetCounter *)
```

但是这里的问题是 `Ref` 是不变的，在构建子类对象的时候，无法将 `self: Ref SubClass` 传递给 `self: Ref SuperClass`。解决方案是将 `Ref` 替换为 `Source`，因为父类只需要读取子类的方法，而不需要修改，并且 `Source` 是协变的。

经过这样的修改，method table 变成每个对象创建时调用一次，而不是每次使用 `self` 时调用一次。

<div class="question">

如何检测 object identity：即检测两个变量指向的是否是同一个对象？

</div>

<div class="answer">

为所有对象都加上一个 `id` 字段，然后为对两个变量的 `id` 字段赋予不同的值，检测两个变量的 `id` 字段是否相等即可。

```ocaml
IdCounterRep = {x: Ref Nat, id: Ref (Ref Nat)};

IdCounter = { get: Unit → Nat, inc: Unit → Unit, id: Unit → (Ref Nat) };

idCounterClass =
  λr:IdCounterRep.
    { get = λ_:Unit. !(r.x),
      inc = λ_:Unit. r.x := succ(!(r.x)),
      id = λ_:Unit. !(r.id) };

sameObject =
  λa:{id: Unit → (Ref Nat) }.
    λb:{ id: Unit → (Ref Nat) }.
      ((b.id unit) := 1;
       (a.id unit) := 0;
       iszero (!(b.id unit)));
```

</div>
