# Finite-Valuation Approximable Structures, Quantum $\lambda$-Calculus, and the Jung–Tix Problem: Semantics and Formal Verification in Lean 4


---

### Abstract
We develop a Lean~4 framework for denotational semantics of an untyped call-by-value $\lambda$-calculus with probabilistic ($\oplus_p$), internal ($\sqcap$), and external ($\Box$) choice, controlled by finite quantum instruments. The intended equation is not the classical Scott equation $D\cong[D\to D]$, nor an effectful collapse $Q\cong[Q\to Q]$. Values inhabit a domain $D_\infty$ and terms denote computations in a quantum-effect layer $Q(D_\infty)$, linked by the call-by-value equation
$$D_\infty\cong[D_\infty\to Q(D_\infty)].$$
Here $Q$ is a monad of computations: unit embeds a value as a trivial computation, and bind sequences an effectful computation with a value-to-computation continuation. Inspired by Chen, Kou, and Lyu’s finite-valuation approximable structures, we define $\omega\mathbf{QVA}$ by requiring approximate identities to factor through finite products of sub-normalized density-operator spaces under the Loewner order; finite spectrahedra are approximation factors, not themselves the power $Q(D)$. We prove a parameterized inverse-limit theorem and instantiate it with the fixed-register continuation power $\mathcal Q_n(D)=[[D\to R_n]\to R_n]$. Finite trace-nonincreasing completely positive (CP) instruments embed into this carrier by Scott-continuous token-local aggregation. The embedding preserves deterministic return exactly and agrees with finite map and bind on finitely presented continuations. Every rational token-theory (TT) test has an explicit Scott representation, so embedding order recovers finitary TT refinement; a directed-supremum obstruction rules out a finite-image Scott retract. On the language side, a hardware qubit Control–Environment–Kontinuation (CEK) machine and subnormalized channel-tree semantics yield final presented channel-tree completeness and token-adequacy capstones for the explicitly witnessed `ClosedStuckFreeCoverage` fragment. This includes restricted ordinary and recursive lambda applications with an external-choice argument; it is not unconditional completeness for every closed term.

---

## Introduction and Background

The Scott–Strachey programme interprets untyped $\lambda$-calculus by solving a reflexive domain equation. Classically one solves $D\cong[D\to D]$: every value is a continuous function from values to values. That equation describes a pure, effect-free universe. Concurrent and nondeterministic computation needs more. Powerdomains (Plotkin, Smyth, Hoare) model internal nondeterminism ($\sqcap$) and external interactive choice ($\Box$). Probabilistic CSP (pCSP) and higher-order probabilistic programming quantify randomized branching by the subprobability valuation powerdomain $\mathcal{V}_{\le 1}$, leading to equations of the form
$$D \cong [D \to \mathcal{P}(\mathcal{V}_{\le 1}(D))].$$
Such equations require a category that is simultaneously Cartesian closed (for $[D\to\dots]$) and closed under $\mathcal{V}_{\le 1}$. In 1998, Jung and Tix identified a persistent obstruction: standard Cartesian closed categories of continuous domains (bifinite, RB, FS) were not known to be preserved by $\mathcal{V}_{\le 1}$. In August 2026, Chen, Kou, and Lyu resolved the Jung–Tix problem by introducing $\omega\mathbf{FVA}$ (finite-valuation approximable domains), the first full Cartesian closed subcategory of continuous domains closed under $\mathcal{V}_{\le 1}$ and $\mathcal{V}_1$.

This paper takes the next step: from classical CSP/pCSP interpretations of $\oplus_p$, $\sqcap$, and $\Box$ on ordinary process or $\lambda$-terms, to a call-by-value interpretation of those same operators as higher-order classical control over a quantum computer. The three choice effects remain distinct classical control operations. They are realized, together with finite completely positive instruments, inside a quantum-effect domain $Q(D_\infty)$. Unitary evolution and measurement are not substitutes for $\oplus_p$, $\sqcap$, or $\Box$.

Call-by-value with effects forces a **value / computation** split. A **monad** $Q$ packages that split: unit $D\to Q(D)$ wraps a value as a trivial computation, and bind $Q(D)\times(D\to Q(E))\to Q(E)$ sequences a computation with a value-to-computation continuation. Untyped call-by-value abstraction then denotes a *value* of function space type $[D\to Q(D)]$—given a value, return a computation—while every *term* denotes an element of $Q(D)$. The matching reflexive equation is therefore
$$D_\infty\cong[D_\infty\to Q(D_\infty)],$$
not $D\cong[D\to D]$ and not $Q\cong[Q\to Q]$.

The contrapositives matter. Solving only $D\cong[D\to D]$ while wanting instruments and choice leaves no place for effects. Solving $Q\cong[Q\to Q]$ would treat computations themselves as the untyped $\lambda$-universe (call-by-name / “everything is a thunk”), contradicting a Control–Environment–Kontinuation (CEK) machine that evaluates the function, evaluates the argument, and only then performs $\beta$-reduction, and contradicting how CP instruments act on values rather than on open computations. The claim of this development is the middle path: untyped call-by-value $\lambda$-calculus with choice and a quantum-effect monad $Q$, values solving $D_\infty\cong[D_\infty\to Q(D_\infty)]$, and terms denoting elements of $Q(D_\infty)$.

The formalized contribution lifts the finite-separation and saturation pattern from classical valuations to quantum spectrahedra ($\omega\mathbf{QVA}$), solves the parameterized equation above for a continuation power $Q=\mathcal Q_n$, and connects the denotation to a qubit CEK machine and channel-tree adequacy fragment. Chen–Kou–Lyu’s classical $\omega\mathbf{FVA}$ theorem and the Jung–Tix history are motivating literature, not a full Lean target of this repository. The Qiskit material below is likewise motivational operational comparison, not a verified compiler or formal equivalence theorem. The later sections state the formal claim and exact Lean boundary.

---

## Syntactic Extension: Untyped $\lambda$-Calculus with Choice Operators

We extend the untyped $\lambda$-calculus with the three canonical choice operators from concurrent and probabilistic process calculi:

$$M, N ::= x \mid \lambda x. M \mid M \, N \mid M \oplus_p N \mid M \sqcap N \mid M \mathbin{\Box} N$$

```mermaid
graph TD
    A["Computational Divergence & Choice"] --> B["Probabilistic Choice (M ⊕_p N)"]
    A --> C["Internal Choice (M ⊓ N)"]
    A --> D["External Choice (M □ N)"]
    B --> B1["Resolved by coin of weight p ∈ [0,1]"]
    C --> C1["Resolved by internal demonic scheduler"]
    D --> D1["Resolved by environment / communication trigger"]
```

### The Three Choice Operators
1. **Probabilistic Choice ($M \oplus_p N$):**
   * **Behavior:** A coin weighted by $p \in [0, 1]$ is flipped at reduction time; the term reduces to $M$ with probability $p$ and to $N$ with probability $1 - p$.
   * **Found in:** Probabilistic $\lambda$-calculus, Probabilistic PCF (Plotkin 1989, Jones 1990, Dal Lago, Ehrhard et al.).
2. **Internal Nondeterministic Choice ($M \sqcap N$ or $M \oplus N$):**
   * **Behavior:** Unpredictable, unobservable scheduling or arbitrary choice between two functions/expressions.
   * **Found in:** De’Liguoro–Piperno’s non-deterministic $\lambda$-calculus, Boudol’s concurrent $\lambda$-calculus.
3. **External / Interactive Choice ($M \mathbin{\Box} N$ or Guarded Selection):**
   * **Behavior:** Waiting for the environment (e.g., awaiting a message on a communication channel or waiting for an argument/input event).
   * **Canonical functional equivalent:** The `select` construct in Concurrent ML (CML) or guarded alternative evaluation:
     $$\text{sync}(\text{receive}(c_1) \Rightarrow \lambda x. M \;\mathbin{\Box}\; \text{receive}(c_2) \Rightarrow \lambda y. N)$$

Classically, giving this calculus a denotational semantics (without quantum effects) means solving something like
$$D \cong [D \to \mathcal{P}(\mathcal{V}_{\le 1}(D))],$$
where $[D \to \dots]$ models higher-order functions, $\mathcal{P}$ models internal choice ($\sqcap$), and $\mathcal{V}_{\le 1}$ models probabilistic choice ($\oplus_p$). In this paper the ambient category is quantum ($\omega\mathbf{QVA}$), application is call-by-value, and effects live in a monad $Q$. The equation we solve is therefore the call-by-value form $D_\infty\cong[D_\infty\to Q(D_\infty)]$ of the previous section, with $\oplus_p$, $\sqcap$, and $\Box$ interpreted as operations on $Q(D_\infty)$ alongside finite CP instruments—not by collapsing them into a pure domain equation $D\cong[D\to D]$ or into $Q\cong[Q\to Q]$.

---

## Motivational Operational Comparison with Qiskit

The tables in this section motivate the denotational semantics by relating two operational presentations through a proposed shared CP denotation. They are not Lean theorems, a literal compiler specification, or a verified Qiskit correspondence. Each row depicts

$$\text{$q\lambda$ construct}\longrightarrow
  \text{CP channel or instrument}
  \longleftarrow\text{Qiskit execution pattern}.$$

For a fixed initial quantum state, the desired equivalence is observational: both sides have the same classical outcome probabilities and, conditioned on an outcome, the same post-measurement quantum state. The quantum forms below are intended primitives extending the classical control syntax of *Syntactic Extension*; they are not Church encodings. Church booleans remain useful classical data, but they are duplicable and therefore cannot stand for qubits. In particular, classical probabilistic choice $M\oplus_p N$ remains a control effect in $Q$, distinct from coherent superposition and from measurement instruments.

### Table 1: Quantum primitives with a shared denotation
| Concept | Intended $q\lambda$ operational form | Qiskit execution pattern | Shared CP denotation |
| :--- | :--- | :--- | :--- |
| **Prepare $\vert0\rangle$** | $\operatorname{new0}(q);\,M$ | `qc.reset(q)` (or a fresh circuit qubit) | Preparation channel with output $\vert0\rangle\langle0\vert$ |
| **Pauli-$X$** | $X(q);\,M$ | `qc.x(q)` | $\rho\mapsto X\rho X^\dagger$ |
| **Prepare $\vert1\rangle$** | $\operatorname{new0}(q);\,X(q);\,M$ | fresh/reset `q`; `qc.x(q)` | Preparation channel with output $\vert1\rangle\langle1\vert$ |
| **Hadamard** | $H(q);\,M$ | `qc.h(q)` | $\rho\mapsto H\rho H^\dagger$; on $\vert0\rangle$ the output is coherent $\vert+\rangle$, not a probabilistic mixture |
| **CNOT** | $\operatorname{CX}(q,r);\,M$ | `qc.cx(q, r)` | $\rho\mapsto \operatorname{CX}\rho\operatorname{CX}^\dagger$ |
| **Measurement** | $\operatorname{measure}\ q\ \operatorname{with}\ 0\Rightarrow M\mid1\Rightarrow N$ | `qc.measure(q, c)` followed by `if_test` branches | Instrument $\Phi_i(\rho)=P_i\rho P_i$; probability $\operatorname{Tr}(\Phi_i(\rho))$ |
| **Classical probabilistic choice** | $M\oplus_p N$ | host RNG, or an ancilla rotation followed by measurement and `if_test` | Branches $p\,\mathrm{id}$ and $(1-p)\,\mathrm{id}$ followed by the denotations of $M,N$ |

### Table 2: Higher-order control and choice
| Concept | $q\lambda$ operational role | Qiskit / host-language counterpart | Denotational correspondence |
| :--- | :--- | :--- | :--- |
| **Variable** | $x$ is classical data or an opaque register handle | Python parameter, classical value, or register index | Environment lookup; a quantum register is threaded by the instrument semantics rather than copied as a Church value |
| **Abstraction** | $\lambda x.M$ packages higher-order classical control | circuit factory, closure, or parameterized subroutine | A value in $[D_\infty\to Q(D_\infty)]$: given a value, return a computation; not necessarily a unitary |
| **Application** | $M\,N$ invokes higher-order control (call-by-value) | call a factory/subroutine and compose its result | Evaluate function and argument as computations, then bind into the body (Kleisli/instrument composition) |
| **Probabilistic choice** | $M\oplus_p N$ resolves by a classical coin | host RNG or measured ancilla controlling dynamic branches | Convex combination of the two computation denotations in $Q(D_\infty)$ |
| **Internal choice** | $M\sqcap N$ is selected by an unobservable scheduler | host/runtime scheduler chooses a branch | Nondeterministic join on computations; no fixed 50/50 probability is implied |
| **External choice** | $M\mathbin{\Box}N$ waits for an environment-selected guard/event | runtime input, callback, or guarded `if_test` | Environment-indexed family of computations; not inherently a controlled unitary |

Thus the “back-and-forth” is between operational realizations at matching semantic layers. Quantum gates and measurements meet as channels and instruments. Untyped $\lambda$ abstraction and application meet Qiskit through the surrounding classical host language as circuit-producing higher-order control. Some terms require dynamic circuits or runtime interaction rather than one static circuit, but the common denotation still supplies the mental bijection used to guide the formal semantics.

---

## Claimed domain equation, Lean dependency map, and status

### Claimed and implemented domain equation

The equation claimed, parameterized, and mechanized is the call-by-value quantum-effect equation of the introduction:

$$
\boxed{\;D_\infty\;\in\;\omega\mathbf{QVA}
\qquad\text{and}\qquad
D_\infty\;\cong\;[D_\infty\to Q(D_\infty)].\;}
$$

#### What $Q$ is

$Q$ is the quantum computation / effect layer on values—not the value domain itself.

| Role | Object | Meaning |
| :--- | :--- | :--- |
| Values | $D_\infty$ | Closures, payloads, what gets substituted |
| Computations | $Q(D_\infty)$ | What a term denotes (effects, choice, instruments) |
| Function space | $[D_\infty\to Q(D_\infty)]$ | A value that, given a value, returns a computation |

A monad on values is specified by unit $D\to Q(D)$ (trivial computation) and bind $Q(D)\times(D\to Q(E))\to Q(E)$ (sequence). Abstractly, $Q$ is any locally continuous, $\omega\mathbf{QVA}$-closed endofunctor of complete lattices equipped with that monadic structure (Lean: `IsQuantumPowerModel` / `IsQuantumMonad`).

**Concrete instance.** The fixed-register continuation power
$$
Q(D)\;=\;\mathcal Q_n(D)\;=\;[[D\to R_n]\to R_n],
$$
where $R_n$ is the continuous lattice of finitary observation results for an $n$-dimensional register (Lean: `TTResult n` / `TTContinuation.model n`). Qubit hardware takes $n=2$. Lean’s existence theorem is `omegaQVA_quantum_domain_equation_solved` in `QLambda/QuantumDomainEquation.lean`. In this presentation $Q$ packages finite quantum instruments together with classical control effects as Scott-continuous maps on result continuations.

#### Contrapositives (what is not claimed)

* **Not** $D\cong[D\to D]$. That is the pure Scott equation; it has no computation monad and no place for instruments or choice as effects.
* **Not** $Q\cong[Q\to Q]$. That would make computations the untyped $\lambda$-universe (call-by-name / thunks), erase the unit/bind layer, and fight both CEK call-by-value evaluation and the fact that CP instruments act on values. Kleisli arrows for $Q$ are maps $[D\to Q(D)]$, not $[Q(D)\to Q(D)]$.
* Abstractions denote elements of $D_\infty$ (lifted by unit into $Q(D_\infty)$); applications denote elements of $Q(D_\infty)$ directly.

### Main Lean module dependencies

```mermaid
flowchart TB
  subgraph vendor["Vendor / Mathlib"]
    Scott["Scott1972 continuous lattices"]
    Mathlib["Mathlib"]
  end

  subgraph domain["Domain construction"]
    Sat["Saturation / OmegaQVA"]
    QP["QuantumPower / Monad"]
    QDE["QuantumDomainEquation<br/>D∞ ≅ [D∞ → Q(D∞)]"]
    Inst["QuantumInstrument / InstrumentPower"]
    Obs["ObservationBasis / RationalCP / TTRefinement"]
    Round["TTRoundedTheory / RoundedTheoryOmega"]
    Cont["TTContinuationMonad<br/>Qn(D)"]
    Emb["TTPhysicalEmbedding"]
    Noncl["FiniteImageNonclosure / ChoiRayObstruction"]
  end

  subgraph language["Language semantics"]
    Syn["Syntax / Operational / Effects"]
    Int["Interp / Soundness"]
    Choice["TTInternal / TTProb / TTExternal / TTComputationChoice"]
    Prim["TTPhysicalPrimitives"]
    Adeq["Adequacy"]
  end

  subgraph hardware["Hardware bridge"]
    Hop["HardwareOperational"]
    Hobs["HardwareObservation"]
    Hlr["HardwareLogicalRelation"]
    Had["HardwareAdequacy"]
    Hch["HardwareChannelSemantics<br/>(layered)"]
  end

  Scott --> Sat
  Mathlib --> Sat
  Sat --> QP
  QP --> QDE
  Sat --> Inst
  Inst --> Obs
  Obs --> Round
  Round --> Cont
  QP --> Cont
  Cont --> Emb
  Emb --> Noncl
  QDE --> Int
  Syn --> Int
  Cont --> Choice
  Emb --> Choice
  Int --> Choice
  Choice --> Prim
  Prim --> Adeq
  Prim --> Hop
  Hop --> Hobs --> Hlr --> Had
  Adeq --> Hlr
  Had --> Hch
```

### Hardware channel submodule dependencies

`QLambda/HardwareChannelSemantics.lean` is a barrel re-export. The proof DAG is linear:

```mermaid
flowchart LR
  Config["Config<br/>trees, relations,<br/>base completeness"]
  Identity["Identity<br/>unique-successor<br/>step transfers"]
  Spines["Spines<br/>NoApp / AdminNoApp<br/>FunAppFrag / Produces<br/>FunFrame stacks"]
  UnderFrame["UnderFrame<br/>under-frame lemmas<br/>closed specials"]
  FunApp["FunApp<br/>fragment inductions<br/>under residual frames"]
  Closed["Closed<br/>closed Produces /<br/>FunAppFrag + tokens"]
  Fundamental["Fundamental<br/>PathChannelEvaluation<br/>closed-term bridge"]
  Productive["Productive<br/>ProductiveClosedCase<br/>restricted extern arguments"]
  Coverage["Coverage<br/>ClosedStuckFreeCoverage<br/>final capstones"]

  Config --> Identity --> Spines --> UnderFrame --> FunApp --> Closed --> Fundamental --> Productive --> Coverage
```

Upstream of `Config`: `HardwareAdequacy` (which rests on `HardwareLogicalRelation`, `HardwareObservation`, `HardwareOperational`, and the TT/adequacy stack above).

Proved claims and exact boundaries are collected in *Claims formalized in
Lean 4* below and indexed compactly in `THEOREMS.md`.

---

## Classical Motivation: Recursive Domain Equations in $\omega\mathbf{FVA}$

This section summarizes the Chen–Kou–Lyu construction used as motivation.
The classical $\omega\mathbf{FVA}$ development and its Jung–Tix theorem are
not formalized here in full. The Lean contribution begins from independently
mechanized finite-separation and saturation ingredients and proves the
quantum $\omega\mathbf{QVA}$ results stated later.

The category $\omega\mathbf{FVA}$ consists of continuous domains $D$ whose identity map is the directed supremum of an increasing sequence of maps factoring through subprobability valuation spaces over finite posets $P_n$:
$$D \xrightarrow{\;p_n\;} \mathcal{V}_{\le 1}(P_n) \xrightarrow{\;e_n\;} D, \qquad \sup_{n \in \mathbb{N}} (e_n \circ p_n) = \mathrm{id}_D$$

The Smyth–Plotkin embedding-projection ($e$-$p$) method proceeds in five steps:

```mermaid
sequenceDiagram
    participant D0 as D₀ = {⊥}
    participant Dn as Dₙ ∈ ωFVA
    participant Dinf as D_∞ = colim Dₙ
    participant Funct as F(D_∞) = [D_∞ → V≤1(D_∞)]
    D0->>Dn: Inductive Functor Application F(Dₙ)
    Dn->>Dinf: Bilimit / Inverse Limit Formation
    Note over Dinf: Saturation Theorem (Thm 6.7(ii))
    Dinf-->>Dinf: Proves D_∞ ∈ ωFVA
    Dinf->>Funct: Isomorphism D_∞ ≅ F(D_∞)
```

### Step 1: Establish the Ambient Cartesian Closed Category ($\omega\mathbf{FVA}$)
By Theorem 10.4 of Chen–Kou–Lyu (2026):
* **Initial / Pointed Object:** $\bot \in D$ exists for all $D \in \omega\mathbf{FVA}$, and the terminal domain $\mathbb{I} = \{\bot\} = \mathcal{V}_{\le 1}(\emptyset)$ is in $\omega\mathbf{FVA}$.
* **Cartesian Closure:** If $X, Y \in \omega\mathbf{FVA}$, then $[X \to Y] \in \omega\mathbf{FVA}$.
* **Probabilistic Closure:** If $X \in \omega\mathbf{FVA}$, then $\mathcal{V}_{\le 1}(X) \in \omega\mathbf{FVA}$ and $\mathcal{V}_1(X) \in \omega\mathbf{FVA}$.

Therefore, the mixed-variance endofunctor $F(X) = [X \to \mathcal{V}_{\le 1}(X)]$ is well-defined internally on $\omega\mathbf{FVA}$.

### Step 2: Build the Approximation Chain via Embedding-Projection Pairs
An embedding-projection pair $(e, p)$ satisfies $p \circ e = \mathrm{id}_X$ and $e \circ p \le \mathrm{id}_Y$.
* **Base stage:** $D_0 = \{\bot\}$.
* **Inductive stages:** $D_{n+1} = F(D_n) = [D_n \to \mathcal{V}_{\le 1}(D_n)] \in \omega\mathbf{FVA}$.
* **Lifting:** 
  $$e_{n+1} = F(e_n, p_n) = [p_n \to \mathcal{V}_{\le 1}(e_n)] : D_{n+1} \to D_{n+2}$$
  $$p_{n+1} = F(p_n, e_n) = [e_n \to \mathcal{V}_{\le 1}(p_n)] : D_{n+2} \to D_{n+1}$$
  yielding the expanding chain: $D_0 \rightleftarrows D_1 \rightleftarrows D_2 \rightleftarrows \dots \rightleftarrows D_n \rightleftarrows \dots$

### Step 3: Take the Bilimit / Colimit $D_\infty$
In $\mathbf{DCPO}$, the bilimit is the standard inverse limit:
$$D_\infty = \left\{ (x_n)_{n \in \mathbb{N}} \in \prod_{n \in \mathbb{N}} D_n \;\middle|\; \forall n, \, x_n = p_n(x_{n+1}) \right\}$$
equipped with canonical limiting pairs $(e_n^\infty : D_n \to D_\infty, \, p_n^\infty : D_\infty \to D_n)$ satisfying $p_n^\infty \circ e_n^\infty = \mathrm{id}_{D_n}$, $e_n^\infty \circ p_n^\infty \le e_{n+1}^\infty \circ p_{n+1}^\infty \le \mathrm{id}_{D_\infty}$, and $\sup_{n \in \mathbb{N}} (e_n^\infty \circ p_n^\infty) = \mathrm{id}_{D_\infty}$.

### Step 4: Proving $D_\infty \in \omega\mathbf{FVA}$ (The Saturation Theorem)
By Theorem 6.7(ii) (Unified Kernel-Lifting / Saturation Theorem):
> If $D$ is a domain with an increasing sequence $a_n = e_n p_n \le \mathrm{id}_D$ such that $\sup_n a_n = \mathrm{id}_D$ factoring through $B_n \in \omega\mathbf{FVA}$, then **$D \in \omega\mathbf{FVA}$**.

Setting $B_n = D_n \in \omega\mathbf{FVA}$ and $a_n = e_n^\infty \circ p_n^\infty$, Theorem 6.7(ii) guarantees **$D_\infty \in \omega\mathbf{FVA}$**.

### Step 5: Establish the Isomorphism $D_\infty \cong [D_\infty \to \mathcal{V}_{\le 1}(D_\infty)]$
Because $F$ preserves directed suprema of embedding-projection pairs:
$$F(D_\infty) = F\left(\operatorname{colim}_n D_n\right) \cong \operatorname{colim}_n F(D_n) = \operatorname{colim}_n D_{n+1} \cong D_\infty$$
Thus, $D_\infty \cong [D_\infty \to \mathcal{V}_{\le 1}(D_\infty)]$ in $\omega\mathbf{FVA}$.

---

## Comparison: $\omega\mathbf{FVA}$ vs. Equilogical Spaces ($\mathbf{Equ}$)

In the late 1990s, semanticists recognized that continuous domains ($\mathbf{CONT}$) failed Cartesian closure and that standard CCC subclasses were not closed under probabilistic valuations. This led to two historical pathways:

```mermaid
graph TD
    A["The 1990s Dilemma: Higher-Order + Probability"] --> B["Strategy A: Categorical Escape"]
    A --> C["Strategy B: Domain Repair from Within"]
    B --> B1["Equilogical Spaces (Equ) - Bauer, Scott"]
    B1 --> B2["Enlarge universe to Quasitoposes via PERs"]
    C --> C1["ωFVA - Chen, Kou, Lyu (2026)"]
    C1 --> C2["Finite-valuation factorizations within continuous dcpos"]
```

1. **Strategy A — Equilogical Spaces ($\mathbf{Equ}$):** Formed by pairs $(X, \sim)$ of $T_0$ spaces with equivalence relations. $\mathbf{Equ}$ is a quasitopos (locally Cartesian closed, handles quotients and sheaves). The trade-off is losing concrete order-theoretic approximations and working with realizers.
2. **Strategy B — $\omega\mathbf{FVA}$:** Retains pure continuous dcpos with Scott topologies and the way-below relation ($\ll$). It resolves the obstruction by replacing finite-image deflations with finite-valuation factorizations ($D \to \mathcal{V}_{\le 1}(P_n) \to D$).
3. **Categorical Embedding:** Every countably based domain in $\omega\mathbf{FVA}$ embeds fully and faithfully into $\mathbf{Equ}$ as $(D, =_D)$:
   $$\omega\mathbf{FVA} \hookrightarrow \omega\mathbf{FS}_\bot \hookrightarrow \mathbf{Equ}$$

### Comparison Table

| Feature | Equilogical Spaces ($\mathbf{Equ}$) | Finite-Valuation Domains ($\omega\mathbf{FVA}$) |
| :--- | :--- | :--- |
| **Mathematical Nature** | Topological spaces + Equivalence relations (Quasitopos) | Partially ordered sets (Continuous DCPOs / FS-domains) |
| **Cartesian Closed?** | **Yes** (by categorical design) | **Yes** (Theorem 10.4) |
| **Probabilistic Monads?** | **Yes** (via realizability/sheaves) | **Yes** ($\mathcal{V}_{\le 1}, \mathcal{V}_1$ are internal functors) |
| **Approximation Theory** | Realizers / Moduli of continuity | Way-below relation ($\ll$) & finite posets $P_n$ |
| **Philosophical Role** | Higher-order probability in topological/categorical logic | Higher-order probability in classical domain theory |

---

## The Quantum Extension: From Classical Probability to $\omega\mathbf{QVA}$

In quantum mechanics, unitary evolution creates coherent superposition, while measurement turns that coherence into a classical distribution of outcomes. For a computational-basis measurement,

$$\alpha\vert 0 \rangle + \beta\vert 1 \rangle
  \xrightarrow{\{\rho\mapsto P_i\rho P_i\}_{i=0,1}}
  \begin{cases}
    0 & \text{with probability } |\alpha|^2,\\
    1 & \text{with probability } |\beta|^2.
  \end{cases}$$

The superposition before measurement is not the probabilistic term $M\oplus_p N$: the latter denotes classical randomized control. Internal scheduler choice $M\sqcap N$ and external guarded choice $M\mathbin{\Box}N$ are two further, independent effects. They do not occur as successive stages after measurement.

### The No-Cloning Barrier and the LNL Architecture
Because the **No-Cloning Theorem** ($|\psi\rangle \not\to |\psi\rangle \otimes |\psi\rangle$) forbids diagonal copy maps $\Delta = \langle \mathrm{id}, \mathrm{id} \rangle$, pure quantum states cannot live directly in a Cartesian Closed Category. Instead, following Selinger and Valiron (2006/2009), we employ a **Linear-Nonlinear (LNL) / Monadic architecture**:

```mermaid
graph LR
    subgraph "Higher-Order Control Layer (Cartesian Closed Category: ωQVA)"
        CC["Functions, Recursion, Closures, Post-Measurement ⊕_p"]
    end
    subgraph "Quantum Computation Monad Q"
        QD["Finite registers, CP trace-nonincreasing maps, instruments"]
    end
    CC -->|Monad Q| QD
```

### Generalizing to $\omega\mathbf{QVA}$
We generalize the Chen–Kou–Lyu construction from commutative probability simplices to non-commutative density operator spaces:

```mermaid
graph LR
    A["Classical ωFVA"] -->|Generalization| B["Quantum ωQVA"]
    A1["Finite Posets P"] --> B1["Finite-dim C*-Algebras A = ⊕ M_d(ℂ)"]
    A2["Simplex Δ≤1(P)"] --> B2["Density Matrices S≤1(A)"]
    A3["Stochastic Order ≤st"] --> B3["Loewner Order ≤L (A ≤L B ↔ B - A ≥ 0)"]
    A4["Convex Polytopes"] --> B4["Convex Spectrahedra"]
    A5["Frontier Erosion Φt"] --> B5["Spectral Projection Depletion Φt"]
```

1. **Finite State Spaces:** Let $A = \bigoplus_{k=1}^m M_{d_k}(\mathbb{C})$. Its sub-normalized density operator space is $\mathcal{S}_{\le 1}(A) = \{ \rho \in A^*_+ \mid \operatorname{Tr}(\rho) \le 1 \}$ equipped with the Loewner partial order $\rho \le_L \sigma \iff \sigma - \rho \ge 0$.
2. **Spectral Depletion Semigroup:** For $\rho = \sum \lambda_i E_i$, $\Phi_t(\rho)$ scales down maximal eigenspace projections, preserving the Loewner order ($\rho \le_L \sigma \implies \Phi_t(\rho) \le_L \Phi_t(\sigma)$) and establishing that $\mathcal{S}_{\le 1}(A)$ is an FS-domain.
3. **Definition ($\omega\mathbf{QVA}$):** A domain $D$ is in $\omega\mathbf{QVA}$ if $\mathrm{id}_D = \sup_n a_n$ where each $a_n$ factors through $\mathcal{S}_{\le 1}(A_n)$ for finite-dimensional $C^*$-algebras $A_n$.
4. **Saturation:** The 2-level flattening lemma (Lemma 6.6) depends only on way-below interpolation ($\ll$) and finite separation, so the bilimit $D_\infty = \operatorname{colim}_n D_n$ lies in $\omega\mathbf{QVA}$. The isomorphism $D_\infty \cong [D_\infty \to \mathcal{Q}(D_\infty)]$ additionally requires a locally continuous endofunctor $\mathcal{Q}$ on $\omega\mathbf{QVA}$.

### The surviving roadmap

The development separates the construction of the semantic domain from the semantics of a language. The broad roadmap that survived formal proof is:

1. **Ambient domain theory — complete.** Define $\omega\mathbf{QVA}$, prove Cartesian closure, prove closure of countable rounded theories, and solve the parameterized inverse-limit equation.
2. **Concrete quantum effect — complete for a fixed register.** Construct the continuation power
   $$\mathcal Q_n(D)=[[D\to R_n]\to R_n]$$
   and prove the functor, local-continuity, $\omega\mathbf{QVA}$-closure, and monad laws required by `IsQuantumPowerModel` and `IsQuantumMonad`.
3. **Finite physical fragment — complete with explicit boundaries.** Embed finite TNI CP instruments into $\mathcal Q_n(D)$; prove exact return and finitely presented map/bind compatibility; prove the represented-test direction of refinement correspondence; and replace the unsupported finite-retract claim by a directed-supremum obstruction theorem.
4. **Language semantics — hardware bridge and covered stuck-free capstone proved.** Terms with closed quantum primitives and recursive abstractions have a compositional Scott-continuous interpretation in $Q(D_\infty)$. A concrete qubit CEK machine carries normalized density states and classical closures and keeps internal, weighted, and external transitions distinct. A separate proof-only subnormalized channel-tree semantics retains all CP branches, including zero-mass branches, and folds them into physical instruments. Runtime logical relations, positive-run correspondence, recursive finite approximants, and token adequacy for each realized channel tree are proved. `ChannelTreeCompleteness` is proved for closed return, Pauli-X, measure-Z, compositional internal and external choice, and probabilistic endpoints; interior probability is complete at presented continuations by physical coin aggregation. Unique-successor identity CEK steps transfer completeness, and recursive denotations are Scott suprema of finite unfoldings. Presented channel-tree completeness and token adequacy are proved for the stacked-application fragments `Produces 0` / `FunAppFrag`, for `ProductiveClosedCase`, and finally for every term carrying `ClosedStuckFreeCoverage`. `RestrictedExternApplication` covers `app (lam …) (extern left right)` and its recursive-lambda analogue under explicit `NoApp`, `AdminNoApp`, and `Atomic` hypotheses. This consolidated boundary is sufficient, not an assertion for every closed term. The rank-one Choi-ray obstruction for `PhysicalBasisApproximant` is formalized for register dimension at least two.

The word “complete” in items 1–3 refers to the stated Lean interfaces and theorems, not to a complete quantum programming language.

### Mini-roadmaps followed during domain construction

#### From finite CP maps to a countable result domain

The first route through Scott-open indicator observations failed to characterize weakest-precondition refinement. `QLambda/RefinementCounterexample.lean` exhibits a rational qubit counterexample over the four-element Boolean diamond: every cumulative Scott-open Choi observation refines, but a monotone Kraus-valued postcondition separates the instruments.

The replacement roadmap was:

1. restrict rational step-postcondition codes to trace-nonincreasing CP maps;
2. test weakest-precondition Choi matrices by finite conjunctions of strict Gaussian-rational quadratic inequalities;
3. identify finitary TT refinement with preservation of all such atoms and tokens;
4. saturate tokens under semantic entailment and strict strengthening;
5. prove the resulting rounded theory is a continuous lattice and an $\omega\mathbf{QVA}$.

Strict inequalities are essential: they provide rational interpolation and allow a finite observation at a directed supremum to be witnessed at a finite stage.

#### From exact pullback to rational local approximation

Exact pullback of a rational Choi test through an arbitrary Kraus family need not remain rational. The successful route therefore used local approximation rather than exact syntactic closure:

1. normalize a `PUnit`-valued finite computation to its total TNI Kraus map;
2. prove uniform bounds for pulled-back Choi functionals on the compact TNI region;
3. approximate each strict functional test by a finite rational quadratic neighbourhood;
4. lift atomwise approximation to finite tokens;
5. use token derivations to extend finite physical operations Scott-continuously to all rounded result theories.

This is implemented across `QLambda/TTResultAlgebra.lean`, `QLambda/TTResultApproximation.lean`, and `QLambda/TTResultOperations.lean`.

#### From a failed compactness shortcut to token-local aggregation

An attempted shortcut treated an entire finitely satisfied result theory as compact. That statement is false in general: a finite instrument can satisfy infinitely many increasingly precise rational observations. The corrected proof works one output token at a time. A bind observation yields finitely many branch-local source tokens; directedness supplies one common continuation stage because the instrument has finitely many outcomes. `AggregateDerives`, `aggregateResult`, `aggregateResult_sSup`, and `bindResultScott` then give the required Scott-continuous aggregation without whole-theory compactness.

#### From an intended order equivalence and retract to the valid boundary

The continuation carrier contains arbitrary Scott-continuous higher-order maps, while the embedding only produces finite-instrument aggregators. Consequently, neither a global order equivalence nor a finite-image retract follows merely from operational agreement on finite presentations.

The proved boundary is explicit:

1. every source rational TT test is represented by a Scott result postcondition and a finite result continuation;
2. consequently, embedding order unconditionally implies `FinitaryTTRefines` for every output code;
3. any Scott projection fixing and landing in the finite image forces that image to be closed under every nonempty directed supremum;
4. therefore any concrete directed family of finite embeddings with a non-finite supremum rules out such a retraction.

The development constructs both the rational coded-test representation and a concrete one-dimensional dyadic-prefix chain of finite embeddings. The chain is directed, while its supremum is separated from every finite embedding by rational coordinate tests. Thus the finite physical image is not closed under directed suprema and admits no Scott-continuous retraction.

### Definitions produced by the construction

- `RatTNICPMatrix n` is a Gaussian-rational Choi matrix with positivity and trace-nonincreasing certificates.
- `FiniteInstrumentComp n D` is a finite family of TNI CP branches returning values in `D`.
- `FinitaryTTRefines C μ ν` quantifies weakest-precondition refinement over rational finite-step postconditions.
- `TTTokenTheory n C` is the saturated rounded completion of finite strict TT tokens.
- `TTResult n` is the fixed result theory at output type `PUnit`.
- `TTContinuationPower n D` is `ScottMap (ScottMap D (TTResult n)) (TTResult n)`.
- `TTPhysicalEmbedding.embed μ` is the Scott-continuous aggregation transformer induced by the finite instrument `μ`.
- `CodedTestRepresentation C c` packages the Scott representation needed to recover a source test `c` from a result continuation.
- `FiniteImageScottRetraction n D` states precisely what a Scott-continuous projection onto the finite embedded image would require.
- `Term Prim` is the untyped source syntax with parameterized closed primitives and recursive function values.
- `SemanticValue Q D₀ j₀` is the solved domain $D_\infty$, while `SemanticComp Q D₀ j₀` is the single term codomain $Q(D_\infty)$.
- `interp primitive M` is a Scott map from environments to $Q(D_\infty)$; `HasComputationChoice` supplies the three still-model-dependent choice operations.
- `RestrictedExternApplication code` records the two proved lambda /
  recursive-lambda applications with an external-choice argument and their
  exact syntactic side conditions.
- `ProductiveClosedCase code` joins the path-productive cases with
  `RestrictedExternApplication`.
- `ClosedStuckFreeCoverage realize code` is the final named sufficient
  coverage boundary for closed presented channel-tree completeness.

### Principal theorems and proof ideas

**Finitary refinement.** `finitaryTTRefines_iff_atom_holds` and `finitaryTTRefines_iff_token_holds` reduce matrix refinement to strict rational quadratic separation. `satisfiedTTTheory_le_iff_finitaryTTRefines` then identifies theory inclusion with the finitary preorder. The forward direction uses Choi monotonicity; the reverse direction separates a failed Loewner inequality by a rational quadratic witness.

**Rounded completion and $\omega\mathbf{QVA}$.** `ttTokenTheory_isContinuousLattice` follows from rounded ideal completion. `RoundedTheory.isOmegaQVA` uses finite-prefix membership gates, each factoring through finite products of one-dimensional sub-normalized density spaces, to approximate the identity.

**Concrete continuation model.** `TTContinuation.model n` satisfies `IsQuantumPowerModel`; the same carrier satisfies `IsQuantumMonad`. Evaluation and precomposition are Scott-continuous, and pointwise directed suprema prove local continuity. Therefore the parameterized theorem `omegaQVA_quantum_domain_equation_solved` applies and yields
$$D_\infty\cong[D_\infty\to\mathcal Q_n(D_\infty)].$$

**Physical embedding.** `bindResultScott_satisfied` proves that on a continuation represented by finite result instruments,
$$\operatorname{embed}(\mu)(k)
  =(\mu\mathbin{\mathrm{bind}}\nu).\operatorname{satisfiedTTTheory}.$$
The proof extracts finitely many branch-local source tokens and extends their semantic derivation to the rounded completion.

**Finite monad compatibility.** `embed_unit` is exact as an equality of Scott maps. `embed_bind_unit` and `embed_unit_bind` inherit the continuation monad unit laws. `embed_map_satisfied` and `embed_bind_satisfied` prove map and Kleisli compatibility on finitely presented result continuations, where physical finite bind has an exact meaning.

**Order boundary.** `finitaryTTRefines_test_of_embed_le` and `finitaryTTRefines_of_embed_le` recover represented rational tests from embedding order. Their proofs evaluate the pointwise Scott-map inequality at the representing continuation and use `satisfiedTTTheory_le_iff_finitaryTTRefines`.

**Retract boundary.** `finiteImage_directedSupClosed_of_retraction` applies preservation of directed suprema by the proposed Scott projection and its fixed-point law. `range_embed_dyadicStage_directed_nonclosed` supplies a concrete non-closure witness, and `no_finiteImageScottRetraction_dyadic` derives the unconditional contradiction.

**Computation-valued interpretation.** `interp_continuous` records that every term clause is Scott-continuous in its environment by construction. `interp_value` proves that ordinary and recursive abstractions are precisely the pure cases lifted through monadic unit. `recLambdaValue_unfold` is Scott’s fixed-point equation for recursive functions. `applyComp_pure_lambda` combines both monad unit laws with the $D_\infty\cong[D_\infty\to Q(D_\infty)]$ inverse equations to prove semantic β-reduction for a pure abstraction and argument.

**Covered stuck-free capstone.**
`closed_term_presented_channelTreeCompleteness_of_productive_case` handles
`ProductiveClosedCase`, including the restricted extern-as-argument forms.
`closed_stuck_free_presented_channelTreeCompleteness` then dispatches every
constructor of `ClosedStuckFreeCoverage`; only its `productiveCase` route
requires `MeasureDistinct`, while `restrictedExtern` uses the direct theorem.
`closed_stuck_free_presented_token_adequacy` composes that result with
presented channel-tree token adequacy. The theorem remains explicitly about
represented continuations and realized finite trees.

### Examples and separating cases

1. **Deterministic return.** A one-outcome identity instrument returning `d` embeds exactly as continuation evaluation at `d`: `embed (unit d) = TTContinuation.unit d`.
2. **Finite sequential composition.** When `k e` is the satisfied result theory of a finite continuation at each returned value, evaluating `embed μ` at `k` equals the satisfied theory of physical instrument bind. The map and bind compatibility theorems are obtained by weakest-precondition semantic equivalence.
3. **Why indicator observations are insufficient.** The Boolean-diamond qubit example proves `ObservationRefines μ ν` while `Refines μ ν` fails. Rational CP-valued step postconditions retain the missing value-dependent quantum information.
4. **Why finite presentations are not assumed compact.** Increasing rational thresholds can approximate a boundary observation indefinitely; token-local witnesses, not a single compact satisfied theory, establish Scott continuity.
5. **One codomain for terms.** A variable does not denote a bare element of $D_\infty$ while an application denotes a computation. Both denote elements of $Q(D_\infty)$; the variable is the special case `unit (ρ x)`. Likewise, an abstraction is folded into $D_\infty$ and then lifted by `unit`.
6. **Recursive function.** The denotation of `recLam self arg body` is the least fixed point of the Scott-continuous self-functional obtained by updating the environment first at `self`, then at `arg`, interpreting `body`, and folding the resulting function back into $D_\infty$. `recLambdaValue_unfold` proves that this value equals one unfolding of that functional.

### Abstract specification and solved domain equation

The finite spectrahedron $\mathcal{S}_{\le 1}(A)$ is an approximation factor in $\omega\mathbf{QVA}$, not the computation type $\mathcal Q(D)$. A quantum power model is instead an assignment $Q$ such that:

1. $Q(D)$ is a complete lattice whenever $D$ is;
2. $Q$ is functorial on Scott maps;
3. $Q$ is order-enriched and locally continuous on monotone $\mathbb N$-families;
4. $D\in\omega\mathbf{QVA}$ implies $Q(D)\in\omega\mathbf{QVA}$.

Let $D_0\in\omega\mathbf{QVA}$ and let $j_0:[D_0\to Q(D_0)]\to D_0$ be a continuous-lattice projection. For the inverse limit of $D_{m+1}=[D_m\to Q(D_m)]$, `omegaQVA_quantum_domain_equation_solved` proves
$$D_\infty\in\omega\mathbf{QVA}
\qquad\text{and}\qquad
D_\infty\cong[D_\infty\to Q(D_\infty)].$$
The mixed tower maps and inverse identities are proved from the specification and instantiate with `TTContinuation.model n`.

### Roadmap from the domain to a complete language semantics

The domain construction supplies the space in which a fixed-register untyped quantum language can be interpreted. A complete semantics still requires the following layers, in this order:

1. **Computation-valued term interpretation — complete for the stated core.** `interp` is compositional and Scott-continuous; renaming, weakening, capture-avoiding value substitution, β, and recursive β are proved.
2. **Operational semantics — hardware core complete.** The CEK machine carries a normalized qubit density matrix, closures, environments, and a continuation stack. Kraus transitions satisfy exact Born normalization and trace bounds.
3. **Probabilistic, internal, and external choice — concrete and separated.** Probability uses physical weighted aggregation, internal choice uses join, and external choice uses explicit branch tags and selectors.
4. **Adequacy — proved at the named covered stuck-free boundary.** Normalized hardware runs model executable positive outcomes; subnormalized channel trees retain every CP branch and fold into finite TNI instruments with exact TT token characterizations. A formal basis-state counterexample rules out reconstructing a state-independent channel from one arbitrary normalized run. Scott recursion is the supremum of finite unfoldings. `ChannelTreeCompleteness` is proved for closed return, Pauli-X, measure-Z, compositional internal and external choice, and probabilistic endpoints; interior probability is complete at presented continuations. Application, argument evaluation, and beta steps transfer completeness by unique-successor identity wrapping. The inductive fragments `FunAppFrag` and `Produces n` give presented completeness for nested lambda / recursive-lambda applications under matching leftover argument frames. `HardwareChannel/Fundamental.lean` assembles path transfer lemmas into `PathChannelEvaluation` / `related_pathChannelTreeTokenAdequacy`. `HardwareChannel/Productive.lean` adds `ProductiveClosedCase` and direct completeness for the restricted extern-as-argument forms. `HardwareChannel/Coverage.lean` proves the final `closed_stuck_free_presented_channelTreeCompleteness` and token theorem for `ClosedStuckFreeCoverage`. Stuck `app (ret) _` states remain excluded (`stuck_payload_under_function_no_internal_step`). A separate rank-one Choi-ray obstruction shows why finitely generated physical-basis approximants cannot interpolate every ray when the register dimension is at least two.

---

## Formal Verification in Lean 4 & Capstone Theorem

The formalization is constructed in Lean 4 on top of the `Scott1972` continuous lattice library (`https://github.com/catskillsresearch/scott1972`). Chen–Kou–Lyu-style finite-separation and saturation lemmas are mechanized in `QLambda/Saturation.lean`, and `omegaQVA_closed_under_functionSpace` proves Cartesian closure by finite-separator step-map sampling. `QLambda/QuantumInstrument.lean` develops finite Kraus instruments and proves residual CP refinement equivalent to Choi order. `QLambda/RefinementCounterexample.lean` proves indicator observations too weak for TT refinement. `QLambda/RationalCP.lean`, `QLambda/TTObservationBasis.lean`, and `QLambda/TTRefinement.lean` replace them by countable physical finitary CP-valued postconditions and prove exact satisfied-theory order correspondence. `QLambda/TTRoundedTheory.lean` forms their saturated continuous completion. `QLambda/RoundedTheoryOmega.lean` proves generically that every encodable rounded basis is an $\omega\mathbf{QVA}$ by explicit one-dimensional density factorizations. `QLambda/TTResultAlgebra.lean`, `QLambda/TTResultApproximation.lean`, and `QLambda/TTResultOperations.lean` establish TNI result normalization, rational local approximation, and Scott-continuous token-local aggregation. `QLambda/TTContinuationMonad.lean` defines $\mathcal Q_n(D)=[[D\to R_n]\to R_n]$, proves every `IsQuantumPowerModel` and `IsQuantumMonad` field, and bundles `TTContinuation.model n`. `QLambda/TTPhysicalEmbedding.lean` embeds finite physical instruments, proves finite monad compatibility on the precisely stated fragment, proves represented-test refinement recovery, and formalizes the directed-supremum obstruction to a finite-image Scott retract.

Language and hardware layers continue from that domain. `QLambda/Interp.lean` and `QLambda/Soundness.lean` give computation-valued interpretation and operational soundness. Choice algebras live in `TTInternalChoice`, `TTProbChoice`, `TTExternalChoice`, and `TTComputationChoice`. The hardware CEK machine and observation/logical-relation stack occupy `HardwareOperational` through `HardwareAdequacy`. Channel-tree completeness is developed in the layered import DAG `QLambda/HardwareChannel/{Config,Identity,Spines,UnderFrame,FunApp,Closed,Fundamental,Productive,Coverage}.lean`, re-exported by `HardwareChannelSemantics.lean`. The compared capstone domain theorem is:

```lean
class IsQuantumPowerModel (Q : (D : Type u) → [CompleteLattice D] → Type u) where
  str : ∀ D [CompleteLattice D], CompleteLattice (Q D)
  map : ∀ {D E} [CompleteLattice D] [CompleteLattice E], ScottMap D E → ScottMap (Q D) (Q E)
  map_id : ...
  map_comp : ...
  map_mono : ...
  map_iSup : ...
  closed : ∀ {D} [CompleteLattice D], IsOmegaQVA D → IsOmegaQVA (Q D)

theorem omegaQVA_quantum_domain_equation_solved
    (M : QuantumPowerModel) (D₀ : QDomain.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor M D₀.carrier)) :
    Nonempty (IsOmegaQVA (QDInf M D₀ j₀)) ∧
    ... ∧
    Nonempty (QDInf M D₀ j₀ ≃o ScottMap (QDInf M D₀ j₀) (QuantumPower M (QDInf M D₀ j₀)))

structure QuantumOperation (n m : ℕ) where
  kraus : List (Matrix (Fin m) (Fin n) ℂ)
  trace_nonincreasing : ...

structure QuantumInstrument (n m outcomes : ℕ) where
  branch : Fin outcomes → List (Matrix (Fin m) (Fin n) ℂ)
  trace_nonincreasing : ...

structure FiniteInstrumentComp (n : ℕ) (D : Type*) where
  Outcome : Type
  [outcomeFintype : Fintype Outcome]
  branch : Outcome → List (Matrix (Fin n) (Fin n) ℂ)
  value : Outcome → D
  trace_nonincreasing : ...

noncomputable def TTPhysicalEmbedding.embed
    (μ : FiniteInstrumentComp n D) :
    TTContinuationPower n D :=
  TTTokenTheory.bindResultScott μ

theorem TTPhysicalEmbedding.embed_unit (d : D) :
    embed (FiniteInstrumentComp.unit (n := n) d) =
      TTContinuation.unit (n := n) d
```

### What the Lean development currently proves (checklist)

1. **Domain.** $D_\infty\in\omega\mathbf{QVA}$ and $D_\infty\cong[D_\infty\to Q(D_\infty)]$ for every quantum power model $Q$, instantiated at $\mathcal Q_n$.
2. **Physical fragment.** Exact `embed_unit`; map/bind agreement on finitely presented continuations; every rational TT test has a Scott representation; embedding order recovers `FinitaryTTRefines`; no Scott retract onto the finite embedded image.
3. **Interpretation.** Compositional Scott-continuous `interp` into $Q(D_\infty)$; ordinary and recursive β; recursive denotations as Scott fixed points / finite-iterate suprema.
4. **Choice.** Internal join, physical weighted probability (not lattice join), and tagged external selection are separated and registered as lawful effect instances.
5. **Hardware adequacy infrastructure.** Normalized CEK machine; subnormalized channel trees; logical relations; token adequacy for realized trees; completeness transfer across unique-successor identity steps.
6. **Covered stuck-free channel-tree capstone.** `FunAppFrag` / `Produces n` under residual frames; `PathChannelEvaluation` and the closed bridges in `HardwareChannel/Fundamental.lean`; `ProductiveClosedCase` and `RestrictedExternApplication` in `HardwareChannel/Productive.lean`; and the consolidated `ClosedStuckFreeCoverage`, `closed_stuck_free_presented_channelTreeCompleteness`, and `closed_stuck_free_presented_token_adequacy` in `HardwareChannel/Coverage.lean`.

A compact status table and the open-hole list appear in the next section.

---

## Claims formalized in Lean 4

### What is proved in Lean (summary)

| Layer | Status | Principal Lean anchors |
| :--- | :--- | :--- |
| $\omega\mathbf{QVA}$, Cartesian closure, saturation | Done | `OmegaQVA`, `Saturation` |
| Parameterized equation $D_\infty\cong[D_\infty\to Q(D_\infty)]$ | Done | `omegaQVA_quantum_domain_equation_solved` |
| Concrete $Q_n$, monad laws | Done | `TTContinuation.model`, `IsQuantumMonad` |
| Finite TNI embedding, presented map/bind, retract obstruction | Done | `TTPhysicalEmbedding`, `FiniteImageNonclosure` |
| Untyped syntax, `interp` in $Q(D_\infty)$, β / rec-β | Done | `Interp`, `Soundness` |
| Prob / intern / extern choice algebras | Done | `TTProbChoice`, `TTInternalChoice`, `TTExternalChoice` |
| Hardware CEK + channel trees + token adequacy infrastructure | Done | `HardwareOperational` … `HardwareAdequacy` |
| Channel-tree completeness: ret, Pauli-X, measure-Z, choice, identity CEK steps | Done | `HardwareChannel/Config`, `Identity` |
| Presented completeness for `Produces` / `FunAppFrag` (incl. `app_lam`, `app_recLam`, FunAppFrag leftover args) | Done (fragment) | `Spines`, `FunApp`, `Closed` |
| Path-indexed fundamental theorem (`PathChannelEvaluation`) | Done | `HardwareChannel/Fundamental` |
| Closed-term presented completeness (NoApp; or any closed term with a branch-complete `PathChannelEvaluation`) | Done | `closed_term_presented_*`, `closed_term_presented_*_of_noApp` |
| Automatic `PathChannelEvaluation` for `Productive 0` (leftover-arity spines, intern-in-body, measure-Z / probability args), nested `app` as an argument, and closed `extern` | Done | `HardwareChannel/Productive`, `closed_term_presented_*_of_productive` |
| Restricted extern arguments under ordinary / recursive lambda, with explicit syntax hypotheses | Done (fragment) | `RestrictedExternApplication`, `ProductiveClosedCase` |
| Consolidated presented completeness and token adequacy for covered closed stuck-free programs | Done (exact boundary) | `ClosedStuckFreeCoverage`, `closed_stuck_free_presented_channelTreeCompleteness`, `closed_stuck_free_presented_token_adequacy` |
| Stuck `app (ret) _` / payload-under-function completeness for arbitrary `realize` | Excluded | `stuck_payload_under_function_no_internal_step` |

### Currently open holes

The following are **not** claimed as proved.

1. **Coverage is sufficient, not exhaustive.** `ClosedStuckFreeCoverage` packages every presently proved closed route, including `RestrictedExternApplication`, but is not a decision procedure or a completeness classification for all non-stuck closed programs.

2. **Restricted extern is exact.** The proved direct forms are `app (lam x body) (extern left right)` and `app (recLam self x body) (extern left right)` under their `NoApp`, `AdminNoApp`, and `Atomic` hypotheses. No claim is made for arbitrary placement or nesting of external choice under residual frames.

3. **Stuck applications.** Stuck `app (ret c) M` reaches a value under a payload function frame (`stuck_payload_under_function_no_internal_step`). For a general `realize`, presented completeness need not hold there, so unrestricted “every closed term” completeness is false.

4. **Interior probability at arbitrary continuations.** For $0<p<1$, completeness is at **finitely presented** continuations (`PresentedChannelTreeCompleteness`). Full `ChannelTreeCompleteness` at arbitrary Scott continuations would need Scott density of presented continuations (or an equivalent approximation argument).

5. **Stronger physical / domain claims not pursued.** A finite-image Scott retract onto embedded instruments is **refuted**, not missing. Raw `InstrumentPower` as an $\omega\mathbf{QVA}$ carrier is not claimed; the Choi-ray obstruction rules out a particular physical-basis approximant scheme for $n\ge 2$, not the continuation-power construction in use.

`arxiv.md` is the narrative status of record; `THEOREMS.md` is the compact
name/file/boundary index.

---

## Acknowledgments & Provenance

* **Software & AI Tooling:** The formalization was mechanized using **Lean 4** and **Mathlib**. The author utilized the **Cursor** development environment, **Grok 4.6 High Fast**, **Gemini 3.7 Flash**, and **GPT-5.6 Sol Medium** as assistive tools for code scaffolding, proof exploration, semantic review, redesign planning, and document drafting.
* **Integrity Statement:** All formal definitions, proofs, and synthesized results were verified under the Lean 4 compiler. Authors retain full and exclusive responsibility for the mathematical correctness of the mechanized proofs and the contents of this manuscript.

---

## References

1. S. Abramsky and B. Coecke. *A categorical semantics of quantum protocols*. In *Proceedings of the 19th Annual IEEE Symposium on Logic in Computer Science (LICS)*, pages 415–425, 2004.
2. P. N. Benton. *A mixed linear and non-linear logic: Proofs, terms and models*. In *Computer Science Logic (CSL)*, LNCS 933, pages 121–135. Springer, 1995.
3. Y. Chen, H. Kou, and Z. Lyu. *Finite-valuation approximable structures: a solution to the Jung–Tix problem of probabilistic powerdomains*. arXiv:2608.03073, 2026.
4. G. Gierz, K. H. Hofmann, K. Keimel, J. D. Lawson, M. Mislove, and D. S. Scott. *Continuous Lattices and Domains*. Cambridge University Press, Cambridge, 2003.
5. C. Jones and G. D. Plotkin. *A probabilistic powerdomain of evaluations*. In *Proceedings of the 4th Annual IEEE Symposium on Logic in Computer Science (LICS)*, pages 186–195, 1989.
6. A. Jung and R. Tix. *The troublesome probabilistic powerdomain*. *Electronic Notes in Theoretical Computer Science*, 13:70–91, 1998.
7. D. S. Scott. *Continuous lattices*. In *Toposes, Algebraic Geometry and Logic*, Lecture Notes in Mathematics, vol. 274, pages 97–136. Springer, Berlin, 1972.
8. P. Selinger and B. Valiron. *A linear-non-linear model for a quantum lambda calculus*. *Information and Computation*, 207(5):603–629, 2009.
9. M. B. Smyth and G. D. Plotkin. *The category-theoretic solution of recursive domain equations*. *SIAM Journal on Computing*, 11(4):761–783, 1982.
10. M. Ying. *Foundations of Quantum Programming*. Morgan Kaufmann / Elsevier, 2016.