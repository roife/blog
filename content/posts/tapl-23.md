+++
title = "[TaPL] 23 Universal Types"
author = ["roife"]
date = 2024-10-04
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论"]
draft = false
+++

上一章提到包含类型变量的表达式在检查时可以有一个 _forall_ 的视角：将类型变量保持抽象，将它替换成任意类型都保证这个表达式是 well-typed 的。这样使得同一份代码可以复用。这就是常见的**泛型**，也就是本章要讨论的 universal types。


## Varieties of Polymorphism {#varieties-of-polymorphism}

允许单一代码片段适用于多种类型的类型系统统称为 _polymorphism_，其有多种表现形式：

-   **Parametric polymorphism**：它允许用类型变量代替具体类型，并在需要时用特定类型进行实例化，并且其所有实例的行为都相同。
    -   Parametric polymorphism 中最强大的形式是 **impredicative polymorphism**，或称作 **first-class polymorphism**，也就是本章介绍的。
    -   实践中另一种常见的形式是上一章介绍的 **let-polymorphism**，其多态性限制在 let-bound 范围内，而不允许函数使用多态类型作为参数。

-   **Ad-hoc polymorphism**：它允许一个值在被视作不同的类型时有不同的行为。
    -   最常见的 ad-hoc polymorphism 就是重载（**overloading**），即同一个函数名可以对应多个不同的实现，编译器根据参数选择实现。将函数重载进行推广，则得到了 multi-method dispatch，其在 \\( \lambda\_\\& \\) 中被形式化。

    -   另一种强大的 ad-hoc polymorphism 是 **intensional polymorphism**。它允许在运行时进行一些受限的类型运算。Intensional polymorphism 是 tag-free garbage collection、unboxed function arguments、polymorphic marshaling、flattened data structures 等高级特性的基础。

    -   还有一种高级的 ad-hoc polymorphism 可以通过 `typecase`（类似 Java 中的 `instanceof`）实现，它允许在运行时对类型进行任意的模式匹配。

-   **Subtype polymorphism**：即前面提到的 subtyping，它允许选择性地忽略部分类型信息（例如将子类型的值看作父类型使用），有时也称为 **inclusion polymorphism**。

这些多态并非互斥，编程语言可以支持其中的多种形式。


## System F {#system-f}

**System F** 一开始在证明论的背景下被发现，后来又在类型系统中发现了其等价的表述，称为**多态 lambda 演算（polymorphic lambda-calculus）**，其被广泛应用于多态性的研究。由于它在 CH 同构下对应于二阶直觉逻辑，因此也被称为**二阶 lambda 演算（second-order lambda-calculus）**。在 System F 中不仅会对 terms（individuals）进行量化，也允许对 types（predicates）进行量化。

System F 是对 STLC 的扩展。在 STLC 中允许利用 lambda abstractions 将 terms 从 terms 中抽取成 abstract term，并利用 applications 为 abstract terms 提供值。类似的，需要引入一种新的机制将 types 从 terms 中抽取出来，称作 **type abstractions**，记为 \\( \lambda X. t \\)，其参数为类型；并进行回填的机制，称为 **type application** 或 **instantiation**，记为 \\( t\ [T] \\)，同样参数为类型表达式。

以 \\( \operatorname{\mathtt{id}} \\) 的定义为例：

\\[\operatorname{\mathtt{id}} = \lambda X. \lambda x: X. x\\]

则 \\( \operatorname{\mathtt{id}}\ [\operatorname{\mathtt{Nat}}] = [X \mapsto \operatorname{\mathtt{Nat}}\]\(\lambda x : X. x) = \lambda x : \operatorname{\mathtt{Nat}}. x \\)

接下来考虑 type abstractions 的类型。在 STLC 中，函数的类型形如 `A -> B`。类似的，type abstractions 也可以用箭头表示，其参数为类型，结果取决于具体的 abstractions。例如 \\( \operatorname{\mathtt{id}} \\) 的类型可以写作 \\( \forall X. X \rightarrow X \\)，其中参数是类型，结果为 \\( X \to X \\)。

下面是 System F 的形式化。

{{< figure src="/img/in-post/post-tapl/23-1-polymorphic-lambda-calculus.png" caption="<span class=\"figure-number\">Figure 1: </span>Polymorphic lambda-calculus (System F)" >}}

类似 STLC，type abstractions 在绑定名字时应当选择上下文中不存在的名字，并且 type abstractions 绑定的变量也可以进行 \\( \alpha \\)-conversion。目前 type variables 的唯一作用是追踪绑定的作用域，保证类型变量名称不会冲突导致错误替换。而在后面将为其添加更多附加信息，例如 bound qualifications。


## Examples {#examples}

通过下面的例子可以看出 System F 的表达能力比 STLC 更强，但是仍然受限于 normalization property，因此比 UTLC 更弱。


### `selfApp` {#selfapp}

在 STLC 中无法写出 \\( \lambda x. x\ x \\) 的类型，但是它能在 System F 中被写出：

\\[ \operatorname{\mathtt{selfApp}} = \lambda x: \forall X. X \to X. x\ [\forall X. X \to X]\ x; \\]
\\[ \operatorname{\mathtt{selfApp}} : (\lambda X. X \to X) \to (\lambda X. X \to X) \\]

此处的 \\( x\ x \\) 中，第一个 \\( x \\) 的类型是 \\( (\forall X. X \to X) \to (\forall X. X \to X) \\)，第二个 \\( x \\) 的类型为 \\( \forall X. X \to X \\)。


### Polymorphic Lists {#polymorphic-lists}

在 STLC 中首次引入 Lists 时，将其相关的操作作为 primitives，然而在 System F 下它们可以被推广为普通函数：

```ocaml
nil : ∀X. List X
cons : ∀X. X → List X → List X
isnil : ∀X. List X → Bool
head : ∀X. List X → X
tail : ∀X. List X → List X
```

类似地可以定义 `map` 函数：

```ocaml
map = λX. λY.
        λf : X → Y.
          (fix (λm : (List X) → (List Y).
                  λl: List X.
                    if isnil [X] l
                      then nil [Y]
                      else cons [Y] (f (head [X] l))
                                    (m (tail [X] l))));
```


### Church Encodings {#church-encodings}

回忆 church encodings 中 booleans 的定义：

```ocaml
tru = λt. λf. t;
fls = λt. λf. f;
```

可以给出二者共有的类型定义：

```ocaml
CBool = ∀X. X → X → X;

tru = λX. λt: X. λf: X. t;
(** tru : CBool *)

fls = λX. λt: X. λf: X. f;
(** fls : CBool *)

not = λb: CBool. λX. λt: X. λf: X. b [X] f t;
(** not : CBool → CBool *)
```

对于数字的定义类似：

```ocaml
c0 = λs. λz. z;
c1 = λs. λz. s z;
c2 = λs. λz. s (s z);
c3 = λs. λz. s (s (s z));
```

对应的 System F 下的类型为：

```ocaml
CNat = ∀X. (X → X) → X → X;

c0 = λX. λs: X → X. λz: X. z;
(** c0 : CNat *)

c1 = λX. λs: X → X. λz: X. s z;
(** c1 : CNat *)

csucc = λn: CNat. λX. λs: X → X. λz: X. s (n [X] s z);
(** csucc : CNat → CNat *)

cplus = λm: CNat. λn: CNat. m [CNat] csucc n;
(** cplus = λm: CNat. λn: CNat. λX. λs: X → X. λz: X. m [X] s (n [X] s z); *)
(** cplus : CNat → CNat → CNat *)

prd2 = λn: CNat. λX. λs: X → X. λz: X.
  n [(X → X) → X]
      (λg: (X → X) → X. λh: X → X. h (g s))
      (λu: X → X. z)
      (λu: X. u);
(** prd2 : CNat → CNat *)
```


### Encoding Pairs {#encoding-pairs}

```ocaml
Pair F S = ∀P. (F → S → P) → P;
pair = λF. λS. λf: F. λs: S. (λP. λp: F → S → P. p f s);
(** pair : Pair *)

fst = λF. λS. λp: ∀P. (F → S → P) → P. p tru
(** fst : ∀F. ∀S. Pair F S → F *)

snd = λF. λS. λp: ∀P. (F → S → P) → P. p fls;
(** snd : ∀F. ∀S. Pair F S → S *)
```


### Encoding Lists {#encoding-lists}

`[a, b]` 在 UTLC 中表示为 `λc.λn.c a (c b n)`。设元素类型为 `X` 的列表类型为 `List X`：

```ocaml
List X = ∀R. (X → R → R) → R → R;
```

其中 `c` 对应 `X → R → R`，`n` 对应 `R`。则：

```ocaml
nil X = (λR. λc: X → R → R. λn: R. n) as List X;
(** nil X : List X *)

cons X = λh: X. λt: List X.
          (λR. λc: X → R → R. λn: R. c h (t [R] c n)) as List X;
(** cons X : X → List X → List X *)

isnil X = λl: List X. l [Bool] (λh: X. λt: Bool. fls) tru;
(** isnil X : List X → Bool *)
```

接下来需要考虑处理 `head`。对于空列表执行 `head` 时，返回的类型也依然应当是 `X`，这就需要能够构造任意类型的 term。回忆之前通过 `diverge` 来构造任意类型的 term，为了实现延迟求值，这里利用 `Unit` 来实现延迟求值：

```ocaml
diverge = λX. λ_: Unit. fix (λx:X. x);
(** diverge : ∀X. Unit → X *)

head X = λl: List X. l [X] (λh: X. λt: X. h) (diverge [X] unit);
(** head X : List X → X *)
```

然而这个定义的问题是在定义时就会触发 diverge。一个更好的方法是将求值推迟到计算结束，为此可以令函数返回 `Unit → X`：

```ocaml
head X = λl: List X.
           (l [Unit→X] (λh: X. λt: Unit → X. λ_: Unit. hd) (diverge [X]))
           unit;
(** head X : List X → X *)
```

定义 `head` 的另一种方案是传入一个默认值，这样就不需要引入 `fix` 了。

为了定义 `tail`，需要先定义 `pair`：

```ocaml
Pair X Y = ∀R. (X → Y → R) → R;
pair : ∀X. ∀Y. X → Y → Pair X Y
fst : ∀X. ∀Y. Pair X Y → X
snd : ∀X. ∀Y. Pair X Y → Y

tail X = λl: List X. (fst [List X] [List X]
         (l [Pair (List X) (List X)]
           (λh: X. λt: Pair (List X) (List X).
             pair [List X] [List X]
               (snd [List X] [List X] tl)
               (cons [X] hd (snd [List X] [List X] tl)))
           (pair [List X] [List X] (nil [X]) (nil [X]))))
(** tail X : List X → List X *)
```


## Properties {#properties}

<div class="theorem">

**(Preservation)**

If \\(\Gamma \vdash t : T\\) and \\(t \to t'\\), then \\(\Gamma \vdash t' : T\\).

</div>

<div class="proof">

证明与 STLC 的 preservation 几乎相同。只是对于 `E-TappTabs` 需要一个类似的额外 lemma：

If \\(\Gamma, X, \Delta \vdash t : T\\), then \\(\Gamma, [X \mapsto S]\Delta \vdash [X \mapsto S]t : [X \mapsto S]T\\).

这里额外的上下文 \\( \Delta\\) 是为了得到更强的归纳假设；如果省略了它，T-Abs 案例将失败。

</div>

<div class="theorem">

**(Progress)**

If \\( t \\) is a closed, well-typed term, then either \\( t \\) is a value or else there is some \\( t' \\) with \\( t \to t' \\).

</div>

<div class="proof">

证明与 STLC 的 progress 几乎相同。但是 canonical forms lemma 需要对新情况进行扩展：

If \\( v \\) is a value of type \\( \forall X.T\_{12} \\), then \\( v = \lambda X.t\_{12} \\).

用于 type application 的情况。

</div>

<div class="theorem">

**(Normalization)**

Well-typed System F terms are normalizing.

</div>

基于 full beta-reduction 的更宽松操作语义的 System F 具有 strong normalization property：every reduction path starting from a well-typed term is guaranteed to terminate.


## Erasure, Typability, and Type Reconstruction {#erasure-typability-and-type-reconstruction}

类似 STLC，可以定义 System F 上的类型擦出函数 `erase`：

<div class="definition">

**(erasure)**

The erasure of a term \\( t \\) in System F is defined as follows:

\begin{aligned}
  & \operatorname{erase}(x) &&= x \\\\
  & \operatorname{erase}(\lambda x : T\_1 . t\_2) &&= \lambda x. \operatorname{erase} (t\_2) \\\\
  & \operatorname{erase}(t\_1\ t\_2) &&= \operatorname{erase}(t\_1)\ \operatorname{erase}(t\_2) \\\\
  & \operatorname{erase}(\lambda X. t₂) &&= \operatorname{erase}(t₂) \\\\
  & \operatorname{erase}(t₁\ [T₂]) &&= \operatorname{erase}(t₁) \\\\
\end{aligned}

</div>

如果在 UTLC 下的 term \\( M \\) 与 System F 下的 well-typed term \\( t \\) 满足 \\( \operatorname{\mathtt{erase}}(t) = m \\)，则称 \\( t \\) 是 typable 的。

System F 的 type reconstruction 问题是 PL 中持续时间最长的问题之一，直到 1990s 初由 Wells 最终解决，并证明是 undecidable 的问题。

<div class="theorem">

**(Wells, 1994)**

It is **undecidable** whether, given a closed term \\( m \\) of the untyped lambda-calculus, there is some well-typed term \\( t \\) in System F such that \\(\operatorname{\mathtt{erase}}(t) = m \\).

</div>

事实上，对于 System F 不仅是 full type reconstruction 是不可判定的，许多 partial type reconstruction 也是不可判定的。例如下面“只重建 application 中的类型变量”的 \\( \operatorname{erase}ₚ \\) 也是不可判定的：

\begin{aligned}
  & \operatorname{erase}ₚ(x) &&= x \\\\
  & \operatorname{erase}ₚ(\lambda x : T\_1 . t\_2) &&= \lambda x. \operatorname{erase}ₚ (t\_2) \\\\
  & \operatorname{erase}ₚ(t\_1\ t\_2) &&= \operatorname{erase}ₚ(t\_1)\ \operatorname{erase}ₚ(t\_2) \\\\
  & \operatorname{erase}ₚ(\lambda X. t₂) &&= \lambda X. \operatorname{erase}ₚ(t₂) \\\\
  & \operatorname{erase}ₚ(t₁\ [T₂]) &&= \operatorname{erase}ₚ(t₁)\ [] \\\\
\end{aligned}

<div class="theorem">

**(Boehm 1985, 1989)**

It is **undecidable** whether, given a closed term \\( s \\) in which type applications are marked but the arguments are omitted, there is some well-typed System F term \\( t \\) such that \\( \operatorname{erase}\_p(t) = s \\).

</div>

Boehm 表明这种形式的 type reconstruction 和 higher-order unification 一样困难，因此也是 undecidable 的。但是这份工作促进了 partial type reconstruction 的发展。并且引发了 first-class existential types 的另一种方法。

事实上，datatype 的 constructors 和 destructors 可以看作显式的类型标注，它们有多个作用，不仅标明了自身所属的 disjoint union types，也标明了 recursive types 需要 fold 和 unfold 的位置，还标明了 existential types 需要packing 和 unpacking 的位置。这一特点被扩展到了 first-class (impredicative) universal quantifiers，经过进一步发展变成了允许程序员显式标注函数参数类型（其中允许使用 universal quantifiers），从而在 ML 和 impredicative sytems 中做了一个折衷。


## Erasure and Evaluation Order {#erasure-and-evaluation-order}

前面给出的 System F 操作语义是 **type-passing semantics**：当多态函数遇到类型参数时，将类型参数替换到函数体中。但是在现实世界的 System F 实现中，这样做可能会带来显著的开销，因为这些类型信息在运行时没有用，不会影响程序的行为。

因此许多语言采用了 **type-erasure semantics**，即类型擦除。在类型检查阶段之后，类型信息被擦除，只剩下无类型项被用于编译。在某些语言中，casting 等特性需要运行时的类型信息，因此这些语言会尝试在运行时保留一种残留形式的类型信息。

然而在现实世界的编程语言中还可能会带有可变引用、异常等副作用特性，这些特性在类型擦除下可能会影响语言行为，因此需要更加精细的 `erase` 函数定义。例如在一个 System F 加异常的系统中，`let f = (λX.error) in 0;` 能够正常求值，而其类型擦除后的结果 `let f = error in 0;` 会抛出异常。这里 type abstraction 在 call-by-value 下会影响语义行为。

这一点类似于在讨论 let-polymorphism 时副作用影响 generalization 的问题。事实上 generalization 的过程就是为一个 erasure 的 term 加上 type abstraction 的过程，即这是类型擦除的相反过程。而 value restrictions 使得程序在存在副作用的情况下强制执行类型擦除，并仅允许 generalization 发生在 term abstractions 和 value constructors 上，从而确保了 soundness。

我们不希望类型影响到程序的 semantics，因此需要修正这种行为：

\begin{aligned}
  & \operatorname{erase}ᵥ(x) &&= x \\\\
  & \operatorname{erase}ᵥ(\lambda x : T\_1 . t\_2) &&= \lambda x. \operatorname{erase}ᵥ (t\_2) \\\\
  & \operatorname{erase}ᵥ(t\_1\ t\_2) &&= \operatorname{erase}ᵥ(t\_1)\ \operatorname{erase}ᵥ(t\_2) \\\\
  & \operatorname{erase}ᵥ(\lambda X. t₂) &&= \lambda X. \operatorname{erase}ᵥ(t₂) \\\\
  & \operatorname{erase}ᵥ(t₁\ [T₂]) &&= \operatorname{erase}ᵥ(t₁)\ \operatorname{\mathtt{dummy}} \\\\
\end{aligned}

此处 `dummy` 是任意 untyped value，使得 type abstraction 在类型擦除后不会延迟求值。并且这样定义的 `erase` 与求值顺序是可交换的，也就是二者以任意顺序执行都不会影响程序的行为。

<div class="theorem">

If \\( \operatorname{\mathtt{erase}}ᵥ(t) = u \\), then either:

1.  both \\( t \\) and \\( u \\) are normal forms according to their respective evaluation relations
2.  \\( t \to t' \\) and \\( u \to u' \\), with \\( \operatorname{\mathtt{erase}}\_v(t') = u' \\)

</div>


## Fragments of System F {#fragments-of-system-f}

由于 System F 上的 type reconstruction 是不可判定的，因此诞生了许多 System F 的受限分支，它们能更好地处理类型推导问题。

最流行的是 ML-style **let-polymorphism**，有时也称为 prenex polymorphism。在 prenex-polymorphism 中，类型变量只能是 monotypes（即类型变量不能包含量词 \\( \forall \\)），并且 polytypes（或称之为 type schemes）不能出现在箭头的左侧（函数参数中）。

System F 另一个分支是 **rank-2 polymorphism**。将类型表示成一棵树（分叉点在 \\( \to \\) 上，注意它是右结合的），如果从树根到一个 \\( \forall \\) 的路径上不会经过大于一次的箭头左侧，则称这个类型是 rank-2 的。例如 \\((\forall X.X \to X) \to \operatorname{\mathtt{Nat}}\\)、\\(\operatorname{\mathtt{Nat}}\to \operatorname{\mathtt{Nat}}\\) 和 \\(\operatorname{\mathtt{Nat}}\to (\forall X.X\to X)\to \operatorname{\mathtt{Nat}} \to \operatorname{\mathtt{Nat}}\\) 都满足条件，但是 \\(((\forall X.X\to X)\to \operatorname{\mathtt{Nat}}) \to \operatorname{\mathtt{Nat}}\\) 不满足条件。这个系统比 prenex polymorphism 要强大一些，并且能够接受更多的 lambda terms。

rank-2 polymorphism 被证明其 type reconstruction 算法复杂度与 prenex polymorphism 相同，并且 rank-3 或更高阶系统上的 type reconstruction 仍然是 undecidable 的。_rank-2_ 的限制并不局限于量词，可以被推广到其他 type constructors。例如 intersection types 也可以定义类似的限制。System F 上的 rank-2 分支与 first-order intersection type system 密切相关，事实上可以证明它们能接受的 lambda terms 范围是相同的。

此外，函数返回值处的 \\( \forall \\) 并不影响判定性，因为有逻辑恒等式：

\\[
P \to \forall x. Q(x) \iff \forall x. P \to Q(x)
\\]

说明函数返回值处的 \\( \forall \\) 可以被移动到头部。


## Parametricity {#parametricity}

观察前面定义的 `CBool`：

```ocaml
CBool = ∀X. X → X → X;

tru = λX. λt: X. λf: X. t;
(** tru : CBool *)

fls = λX. λt: X. λf: X. f;
(** fls : CBool *)
```

可以发现 `CBool` 的定义与 `tru` 和 `fls` 的定义高度对称。其中 \\( \forall X \\) 与 \\( \lambda X \\) 相对，\\( X \to X \to \\\_ \\) 与 \\( \lambda t: X. \lambda f: X \\) 相对，\\( \to X \\) 与 \\( t / f \\) 相对。由于返回值是 \\( X \\)，因此这里要么返回 \\( t \\)，要么返回 \\( f \\)。可以看出多态程序与它们的类型高度相关（尽管可以构建其他 `CBool` 的 term，但是它们的行为都与 `tru` 和 `fls` 等价）。

**Parametricity** 表明被实例化的多态程序的行为满足某种统一的模式，这种模式与其多态类型有关。从多态类型中就可以观察它被实例化后的各种程序，无论其传入什么类型，函数的行为都是统一的。这正好与 ad-hoc polymorphism 相反，因为后者的行为取决于实例化后的类型，不同类型的参数所执行的行为可能截然不同。

换句话说，给定一个参数化多态类型，倘若将行为一致的实例看成相同实例，那所有实例可以从类型里得到。因此想要在实例集合上做证明，那么可以直接在其多态类型上进行证明。

Parametricity 可以看成 abstraction 的对偶。前者对函数内部实现隐藏了外部世界调用时的具体类型，而后者对外界隐藏了内部实现。


## Impredicativity {#impredicativity}

如果一个定义（例如集合、类型等）中涉及到了一个域是自身的量词，那么称它是 **impredicative** 的。

System F 的多态是 **impredecative** 的。例如类型定义 \\( T = \forall X. X \to X \\) 中 \\( X \\) 就可以是自身，即定义出 \\( T [T] = T \to T \\)。而 ML 中的多态是 predicative 的（或 stratified 的），因为它只允许 monotype 作为参数，不允许将包含量词的类型作为参数。

Predicativity 的说法来自于逻辑学。罗素在处理罗素悖论（\\( x \\) 不是 \\( x \\) 的成员）时发现，悖论的根源在于 membership 条件中的自指涉，即条件中的 \\( x \\) 与正在定义的 \\( x \\) 相同，因此罗素将这种 membership 条件称为 **impredicative**。罗素认为一个 predicate 确定了一个 class，而 impredicative 的条件不能作为 predicates，它们不能构成一个 class，因此也不允许它成为 class，从而解决了罗素悖论。而后 predicativity 便用于集合论，指那些允许自指涉的定义。
