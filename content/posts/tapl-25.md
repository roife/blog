+++
title = "[TaPL] 25 An ML Implementation of System F"
author = ["roife"]
date = 2024-10-11
series = ["Types and Programming Languages"]
tags = ["类型系统", "程序语言理论"]
draft = false
+++

## Nameless Representation of Types {#nameless-representation-of-types}

前面在实现时使用 de Bruijn index 来表示变量。在 System F 中，变量也可以使用 \\( \forall \\) 进行绑定，这一点类似于 lambda abstractions，并且也会出现替换和重命名的问题。为了解决这个问题，这里也可以同样利用 de Bruijn index 来表示类型。

```ocaml
type ty =
  TyVar of int * int
| TyArr of ty * ty
| TyAll of string * ty
| TySome of string * ty
```

此处 `TyVar` 的第一个参数表示它相对于 binding 的深度，第二个参数表示上下文的长度。`TyAll` 和 `TySome` 中的字符串表示绑定的变量名，只用于打印结果。

接下来扩展 context，添加对于类型的绑定：

```ocaml
type binding =
  NameBind
| VarBind of ty
| TyVarBind
```

这类对类型变量的绑定和对变量的绑定类似，只用于区分而不需要携带额外信息。


## Type Shifting and Substitution {#type-shifting-and-substitution}

Type abstractions 的处理和 lambda abstractions 类似，可以定义 shifting：

<div class="definition">

**(Shifting)**

The **\\(d\\)-place shift** of a type \\(T\\) above cutoff \\(c\\), written \\(\uparrow^d\_c (T)\\), is defined as follows:

\begin{alignat\*}{2}
&\uparrow^d\_c(k) &&=
    \begin{cases}
        k & \text{if $k < c$} \\\\
        k+d & \text{if $k \ge c$}
    \end{cases}\\\\
&\uparrow^d\_c(T₁ \to T₂) &&= \uparrow^d\_c(T₁) \to \uparrow^d\_c(T₂) \\\\
&\uparrow^d\_c(\forall. t\_1) &&= \forall. \uparrow^{d}\_{c+1} (t\_1) \\\\
&\uparrow^d\_c\\{\exists, t\_1\\} &&= \\{ \exists, \uparrow^{d}\_{c+1} (t\_1) \\} \\\\
\end{alignat\*}

\\(\uparrow^d\_0 (t)\\) 可以记作 \\(\uparrow^d (t)\\)

</div>

将其翻译为 OCaml 代码：

```ocaml
let typeShiftAbove d c tyT =
  let rec walk c tyT = match tyT with
      TyVar(x, n) -> if x >= c then TyVar(x+d, n+d) else TyVar(x, n+d)
    | TyArr(tyT1, tyT2) -> TyArr(walk c tyT1, walk c tyT2)
    | TyAll(tyX, tyT2) -> TyAll(tyX, walk (c+1) tyT2)
    | TySome(tyX, tyT2) -> TySome(tyX, walk (c+1) tyT2)
  in walk c tyT
```

事实上，这个函数可以和用于 substitution 的 `typeSubst` 复用。考虑其 substitution 的定义：

\begin{aligned}
&[j \mapsto s]k &&=
  \begin{cases}
      s & \text{if $k = j$} \\\\
      k & \text{otherwise}
  \end{cases}\\\\
&[j \mapsto s\]\(T₁ \to T₂) &&= ([j \mapsto s]T₁\ [j \mapsto s]T₂) \\\\
&[j \mapsto s\]\(\forall. t\_1) &&= \forall. [j+1 \mapsto \uparrow^1 s]t\_1 \\\\
&[j \mapsto s]\\{\exists, t\_1\\} &&= \\{ \exists, [j+1 \mapsto \uparrow^1 s]t\_1 \\}
\end{aligned}

不难发现除了最基本的情况，其他情况和 shifting 一样。因此可以定义一个统一的函数：

```ocaml
let tymap onvar c tyT =
  let rec walk c tyT = match tyT with
      TyArr(tyT1,tyT2) -> TyArr(walk c tyT1,walk c tyT2)
    | TyVar(x,n) -> onvar c x n
    | TyAll(tyX,tyT2) -> TyAll(tyX,walk (c+1) tyT2)
    | TySome(tyX,tyT2) -> TySome(tyX,walk (c+1) tyT2)
  in walk c tyT

let typeShiftAbove d c tyT =
  tymap (fun c x n -> if x>=c then TyVar(x+d,n+d) else TyVar(x,n+d))
    c tyT

let typeShift d tyT = typeShiftAbove d 0 tyT

let typeSubst tyS j tyT =
  tymap
    (fun j x n -> if x=j then (typeShift j tyS) else (TyVar(x, n)))
    j tyT
```

Type abstraction 的 beta-reduction 和 lambda abstraction 相同：

```ocaml
let typeSubstTop tyS tyT =
  typeShift (-1) (typeSubst (typeShift 1 tyS) 0 tyT)
```


## Terms {#terms}

System F 上的 terms 相比 STLC 多了 pack 和 unpack 的步骤：

```ocaml
type term =
  TmVar of info * int * int
| TmAbs of info * string * ty * term
| TmApp of info * term * term
(* forall *)
| TmTAbs of info * string * term (* forall X. T *)
| TmTApp of info * term * ty     (* T [x] *)
(* exists *)
| TmPack of info * ty * term * ty (* {*X. t} as T *)
| TmUnpack of info * string * string * term * term (* let {X, x}=t in t' *)
```

类似 types，terms 的 shifting 和 substitution 也可以统一处理：

```ocaml
let tmmap onvar ontype c t =
  let rec walk c t = match t with
      TmVar(fi, x, n) -> onvar fi c x n
    | TmAbs(fi, x, tyT1, t2) -> TmAbs(fi, x, ontype c tyT1, walk (c+1) t2)
    | TmApp(fi, t1, t2) -> TmApp(fi, walk c t1, walk c t2)
    | TmTAbs(fi, tyX, t2) -> TmTAbs(fi, tyX, walk (c+1) t2)
    | TmTApp(fi, t1, tyT2) -> TmTApp(fi, walk c t1, ontype c tyT2)
    | TmPack(fi, tyT1, t2, tyT3) ->
       TmPack(fi, ontype c tyT1, walk c t2, ontype c tyT3)
    | TmUnpack(fi, tyX, x, t1, t2) ->
       TmUnpack(fi, tyX, x, walk c t1, walk (c+2) t2)
  in walk c t
```

注意此处 `Unpack` 定义中，进入 `t2` 是 `c+2`，因为在计算时 `X` 和 `x` 都会被添加到上下文，因为上下文长度实际上增长了 2。

注意这里不仅有 `onvar`，还有 `ontype`。这是因为在 terms 中不仅包含了 terms，还包含了 types，后者需要 `tymap` 处理。注意在 terms 的 substition 时，不需要对 types 进行处理。

```ocaml
let termShiftAbove d c t =
  tmmap
    (fun fi c x n -> if x >= c then TmVar(fi, x+d, n+d)
                     else TmVar(fi, x, n+d))
    (typeShiftAbove d)
    c t
let termShift d t = termShiftAbove d 0 t

let termSubst j s t =
  tmmap
    (fun fi j x n -> if x=j then termShift j s else TmVar(fi, x, n))
    (fun j tyT -> tyT)
    j t

let termSubstTop s t =
  termShift (-1) (termSubst 0 (termShift 1 s) t)
```

此外还需要定义对于 terms 中类型变量的替换，此处对于 `TmVar` 的处理实际上是一个恒等函数，直接返回本身：

```ocaml
let rec tytermSubst tyS j tyT =
  tmmap
    (fun fi j x n -> TmVar(fi, x, n))
    (fun j tyT -> typeSubst tyS j tyT)
    j tyT

let tytermSubstTop tyS t =
  termShift (-1) (tytermSubst (typeShift 1 tyS) 0 t)
```


## Evaluation {#evaluation}

```ocaml
let rec eval1 ctx t = match t with
    ...
  | TmTApp(fi, TmTAbs(_, x, t11), tyT2) ->
     tytermSubstTop tyT2 t11
  | TmTApp(fi, t1, tyT2) ->
     let t1' = eval1 ctx t1 in
     TmTApp(fi, t1', tyT2)
  | TmUnpack(fi, _, _, TmPack(_, tyT11, v12, _), t2) when isval ctx v12 ->
     tytermSubstTop tyT11 (termSubstTop (termShift 1 v12) t2)
  | TmUnpack(fi, tyX, x, t1, t2) ->
     let t1' = eval1 ctx t1 in
     TmUnpack(fi, tyX, x, t1', t2)
  | TmPack(fi, tyT1, t2, tyT3) ->
     let t2' = eval1 ctx t2 in
     TmPack(fi, tyT1, t2', tyT3)
```

Evaluation 的过程基本是对 STLC 的拓展。这里值得注意的是第三条 `Unpack` 规则，其对应的 rules 是 `[X -> tyT11] [x -> v12] t2`。其中 `t2` 的形式为 \\( \\{ \exists X. T\\} \\)，因此最外层的是 \\( X \\)，然后是 \\( x \\)，因此在替换 `v12` 前需要对其进行 shifting。


## Typing {#typing}

```ocaml
let rec typeof ctx t =
  match t with
    TmVar(fi, i, _) -> getTypeFromContext fi ctx i
  | TmAbs(fi, x, tyT1, t2) ->
     let ctx' = addbinding ctx x (VarBind(tyT1)) in
     let tyT2 = typeof ctx' t2 in
     TyArr(tyT1,  typeShift (-1) tyT2)
  | TmApp(fi, t1, t2) ->
     let tyT1 = typeof ctx t1 in
     let tyT2 = typeof ctx t2 in
     (match tyT1 with
        TyArr(tyT11, tyT12) ->
         if (=) tyT2 tyT11 then tyT12
         else error fi "parameter type mismatch"
      | _ -> error fi "arrow type expected")
  | TmTAbs(fi, tyX, t2) ->
     let ctx = addbinding ctx tyX TyVarBind in
     let tyT2 = typeof ctx t2 in
     TyAll(tyX, tyT2)
  | TmTApp(fi, t1, tyT2) ->
     let tyT1 = typeof ctx t1 in
     (match tyT1 with
        TyAll(_, tyT12) -> typeSubstTop tyT2 tyT12
      | _ -> error fi "universal type expected")
  | TmPack(fi, tyT1, t2, tyT) ->
     (match tyT with
        TySome(tyY, tyT2) ->
         let tyU = typeof ctx t2 in
         let tyU' = typeSubstTop tyT1 tyT2 in
         if (=) tyU tyU' then tyT
         else error fi "doesn't match declared type"
      | _ -> error fi "existential type expected")
  | TmUnpack(fi, tyX, x, t1, t2) ->
     let tyT1 = typeof ctx t1 in
     (match tyT1 with
        TySome(tyY, tyT11) ->
         let ctx' = addbinding ctx tyX TyVarBind in
         let ctx'' = addbinding ctx' x (VarBind tyT11) in
         let tyT2 = typeof ctx'' t2 in
         typeShift (-2) tyT2 (* 因为 X 和 x 都已经被替换，所以完成后 ctx 长度会减小 2 *)
      | _ -> error fi "existential type expected")
```

前面在 existential types 中提到，如果 `let` 的结果类型是 \\( \\{ \exists X, T \\} \\) 中的 \\( X \\)，那么应该报 `scopeing error`。其实现方式为，如果 `t2` 中包含了 `X`，那么在计算完成后其对应的类型为 `TyVarBind`，对应 `0`。经过 `-2`，其值变为负数，可以利用这一点，实现检测：

```ocaml
let typeShiftAbove d c tyT =
  tymap
    (fun c x n -> if x>=c then
                    if x+d<0 then err "Scoping error!"
                    else TyVar(x+d, n+d)
                  else TyVar(x, n+d))
    c tyT
```
