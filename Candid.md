---
layout: post
title: Candid
---

# Candid: A Classical Theorem Prover
[Candid](https://github.com/david-davies/prover) is a functional programming language with dependent types and control operators (think call/cc from Scheme). By making certain value-like restrictions for dependent typings, it also doubles up us a theorem prover for classical (first order) logic. 

This means we can prove classical properties with computational meaning!

## Basics
The new operator is: ``\\α.[β]``, which in the literature looks like `μα.[β]`. It means to capture the current (evaluation) context by `α`, and then switch to the context captured by `β`. We call `α` a mu-variable, or continuation variable.

### Contexts
A context can be thought of as the stack when evaluating the term. For those interested, a good point of view on what a context is by seeing the [$λμ\tilde{μ}$ calculus](https://hal.inria.fr/file/index/docid/156377/filename/icfp-CuHer00-duality_errata.pdf), and how it is able to control the context.

In our case, the context of $m$ in a term $A:=p_1 p_2 m q_1 q_2$ is essentially the surrounding terms; $\mathcal{C}:=p_1 p_2 \bullet q_1 q_2$. $\bullet$ represents the 'hole' in the context, which is waiting to have a term inserted into it. To regain the original term $A$, we can insert $m$ into the context $\mathcal{C}$, done with notation $\mathcal{C}\{m\}$.

Formally, we can define contexts by:
$$\mathcal{C} ::= \bullet \mid \mathcal{C}\ n 
\mid m\ \mathcal{C} 
\mid c_i\ \vec{m}\ \mathcal{C}\ \vec{n}
\mid p_i( \mathcal{C})
\mid \textsf{case}\ \mathcal{C}\ \textsf{of } \overrightarrow{\textsf{alts}}
\mid \textsf{elim}\ \mathcal{C}\ \textsf{of } \overrightarrow{\textsf{alts}}
\mid \textsf{build}\ (\vec{m}\mid\mathcal{C}\mid\vec{n})$$
Here, $c_i$ represents a data constructor, and $p_i$ a codata/record projection. $\vec{m}=m_1\ m_2 \cdots m_k$ is a vector of 0 or more terms.

We can then succinctly write the way a `\\α` term evaluates:
```
𝓒{\\α.m} --> \\α.m[ [α]𝓒{n} / [α]n ]
```
Where `m[ [α]𝓒{n} / [α]n ]` means to replace, in `m`, every subterm of the form `[α]n` with `[α]𝓒{n}`. Roughly speaking, we insert every `α`-subterm into the context `𝓒`.

The range of a context that a `\\α` can capture is limited by lambdas and other `\\β[γ]` terms. 

A note: in the actual theory and implementation, the contexts have to be split into call-by-value contexts for all terms, except for the $\textsf{build}$ terms which have to be lazily evaluated. This is because $\textsf{build}$ defines a codata term by its projections, so can be potentially infinite.

### Examples
- Simple Example:
```
    (\\α.[α] f (\\β.[α] g)) x y
--> (\\α.[α] f (\\β.[α] g x) x) y
--> (\\α.[α] f (\\β.[α] g x y) x y)
```
- `\\_` means that `_` is a mu variable that doesn't appear in the subterm; it effectively throws away its context:
```
    f v1 v2 (\\_.[α] g x) y1 y2 y3
--> f v1 (\\_.[α] g x) y1 y2 y3
--> f (\\_.[α] g x) y1 y2 y3
...
--> (\\_.[α] g x) y3
--> \\_.[α] g x 
```




- E.g. We assume there's some continuation variable `β` in the environment. Here `\\_` means that the context is essentially thrown out
```
    \\α.[β] f (\\_.[α] g) x y
--> \\α.[β] f (\\_.[α] g x) y
--> \\α.[β] f (\\_.[α] g x y)
--> \\α.[β] (\\_.[α] g x y)
--> \\α.[α] g x y
--> g x y
```

### Call/CC, Catch and Throw

Call/cc:
```haskell
callcc y = \\α.[α] y (\x -> \\_.[α] x)
```

Those familiar with exception style `catch` and `throw` operators can understand them as `\\α.[α]` and `\\_.[α]` respec. The difference is that the handler must be given to the `throw` as an argument.

The catch/throw monad in (e.g.) haskell is quite different, and we show how to implement a similar mechanism in a pure (non-monadic) environment:

Some preamble:
```haskell
-- Unit Type
data ⊤ : Type where
    <> : ⊤

-- A 'thunked' evaluation context
Ctx : (A : Type) -> Type
Ctx A = ⊤ -> A
```

Defining the macros:

```haskell
catch : (A : Type) -> (Ctx A -> A) -> A -> A
catch _ program handler = \\α.[α] program (\_ -> \\_.[α] handler)

throw : (A : Type) -> (Ctx A) -> A
throw _ ctx = ctx <>
```

Now this can be used a lot like the haskell catch/throw monad. Assume we have natural numbers defined, and a subtract function that throws to a given context if the result is less than zero.

```haskell
p : Nat
p = catch Nat (subtract 1 2) 5
```
`p` will evaluate to `5`.

### Law of Excluded Middle, 
```haskell
lem : (A : Type) -> (A + !A)
lem _ = \\`a.[`a] inj2 (\x -> \\_.[`a] inj1 x)
```

### First Order Classical Notion

We want to show `Q:=¬∀x.¬B(x) -> ∃x.B(x)`. This is a classical proposition, not provable in intuitionistic logic; as there is no actual `x` that can be constructed to prove the existential. In Candid, we can prove this. We first prove a lemma `P`, and then prove `Q`.
```haskell
-- ¬∃x.B(x) -> ∀x.¬B(x)
P : (A : Type) -> (B : A -> Type) 
    -> !((n:A) * B n) 
    -> ((n:A) -> !(B n))
P _ _ nex = \n b_n -> nex (n, b_n)

-- ¬∀x.¬B(x) -> ∃x.B(x)
Q : (A : Type) -> (B : A -> Type) 
    -> !((n:A) -> !(B n)) 
    -> ((n:A) * B n)
Q A B nfa = \\nex.[_] nfa (P A B (\x -> \\_.[nex] x))
```


