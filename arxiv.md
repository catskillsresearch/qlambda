# Domain Semantics and Circuit Completeness for a Typed Linear Quantum $\lambda$-Calculus Formalized in Lean 4

---

## Abstract

We present a Lean 4 formalization of a typed linear/nonlinear quantum
$\lambda$-calculus.  Separate unrestricted and linear contexts enforce that
quantum data cannot be copied or discarded implicitly.  The language has
linear and unrestricted functions, tensor products, classical bits, qubits,
strictly positive recursive types, allocation, unitary gates, reset, and
measurement.  Probability is not a source-language choice operator: it arises
only from quantum measurement.

The semantic target is a type-indexed linear/nonlinear model based on quantum
sets, quantum relations, and quantum CPOs.  Finite completely positive maps
and instruments provide the first-order meanings of gates and measurement,
while recursive types are represented by compatible chains of finite
unfoldings.  A separate finite fragment stages deterministically to a typed
circuit normal form and then to a versioned IBM Composer/OpenQASM subset.

The mechanization required detailed proofs for which we found no reusable
machine-checked development in the cited quantum-relation and qCPO
literature.  In particular, we give new Lean proofs that the relevant
quantum-relation homs are
complete lattices, that relational composition preserves countable joins in
both arguments, that daggers reverse composition, that quantum functions
compose, and that discrete quantum posets satisfy the quantum-CPO completeness
condition.  To our knowledge, this is also the first machine-checked
construction of the compact-closed quantum-relation structure together with
the concrete ordinary adjunction
$\mathsf{Set}\leftrightarrows\mathsf{qRel}$ in this representation, and the
first certified typed lambda quotation theorem for the declared two-wire
Composer fragment.  These are novel formal proofs, not claims that every
underlying mathematical statement is new; the priority wording is limited by
the literature audit described below.

The present theorem boundary is explicit.  Source typing, substitution,
preservation, runtime progress, measurement normalization, deterministic
staging, the quantum-relation enrichment, and structured OpenQASM
parse/render round trips are kernel checked.  So are the concrete quantum LNL
instance, the Scott-function qCPO category, continuous projection-chain
fold/unfold maps, and canonical two-wire lambda/circuit completeness.  The
generic compositional denotation interface and exact operational quotient do
not amount to full abstraction or unrestricted computational adequacy for
arbitrary recursive programs; we make neither claim.  Full sources are at
https://github.com/catskillsresearch/qlambda.

---

## 1. Introduction

Quantum programming combines two incompatible structural regimes.  Classical
data may be weakened and contracted; unknown quantum data may not be copied,
and its disposal must be represented by a physical operation.  A semantics
that puts both kinds of values in an ordinary Cartesian context obscures this
distinction.  We instead use a linear/nonlinear judgment

$$
\Gamma;\Delta\vdash M:A,
$$

where $\Gamma$ contains unrestricted assumptions and $\Delta$ contains
exactly-once assumptions.  A derivation is intended to denote a morphism

$$
F\llbracket\Gamma\rrbracket\otimes\llbracket\Delta\rrbracket
\longrightarrow \llbracket A\rrbracket
$$

in an $\omega$CPO-enriched LNL model.

This is a typed, type-indexed account.  It does not use a universal untyped
reflexive object, and it does not put all effects into a central continuation
monad.  Each admissible recursive type has its own approximation chain.
Quantum evolution is represented by linear morphisms; measurement is the
source of probabilistic branching.

### Contributions

The development has four connected parts.

1. It gives a Church-style linear/nonlinear quantum $\lambda$-calculus with
   de Bruijn syntax, verified formation predicates for recursive types,
   substitution, preservation, and a finite-register operational semantics.
2. It formalizes quantum-set and quantum-relation algebra, including complete
   hom orders, $\omega$-continuous composition, compact closure, the concrete
   $\mathsf{Set}\dashv\mathsf{qRel}$ LNL model, and a separate category of
   quantum CPOs and Scott-continuous quantum functions.
3. It constructs a deterministic, resource-certified staging procedure from
   a closed terminating first-order fragment to circuit normal form.
4. It gives canonical typed lambda quotation for a two-wire circuit fragment
   and a structured Composer/OpenQASM interchange with ideal
   classical--quantum denotation and canonical parse/render theorems.

The first substantial formalization obligation not available as an
off-the-shelf machine-checked library was the enriched algebra of quantum
relations. Weaver, Kornell, Jenča--Lindenhovius, and
Kornell--Lindenhovius--Mislove prove stronger paper-level categorical
results, but provide no Lean implementation of the chosen matrix/subspace
representation. We prove
the complete hom lattice, bilateral join-continuity of composition, closure
of functions under composition, and the discrete-qCPO instance directly.
The higher-order development further proves explicit tensor,
evaluation/currying, unitors, associator, braiding, and the ordinary strong
monoidal adjunction.  In particular it does not use the false route from
pointwise-ordered continuous maps to graph relations: graph is used from a
discretely ordered ordinary set category.

### Scope

“Circuit completeness” means that every circuit in the declared finite target
fragment has a canonical well-typed lambda representative.  It does not mean
that every unitary has an exact finite decomposition.  OpenQASM is an
interchange format here, not the denotational semantics, and no result concerns
calibration, noise, transpiler heuristics, or arbitrary Python/Qiskit programs.

---

## 2. The Typed Linear Language

Types are

$$
A,B ::= \alpha \mid 1 \mid \mathsf{Bit}\mid\mathsf{Qubit}
       \mid A\otimes B
       \mid A\multimap B
       \mid A\to B
       \mid \mu\alpha.A.
$$

The two arrows correspond to linear and unrestricted binders.  The term
syntax uses lambda as its only binder.  Tensor and measurement elimination are
continuation based, which avoids adding ad hoc binding constructs.

The physical primitives are fresh-$|0\rangle$ allocation, $X$, $H$, $T$,
rational-angle $RY$, saturated $CX$, reset, and measurement.  Measurement
consumes a linear qubit and passes both the classical result and the
post-measurement qubit to its continuation.  There is no `emit`, source
sequencing primitive, probabilistic choice, internal choice, or external
choice.

### 2.1 Contexts and typing

Unrestricted variables may be weakened and contracted.  A linear context is a
list of optional type cells; context splitting partitions occupied cells while
preserving de Bruijn positions.  Linear application and tensor introduction
split the linear context.  An unrestricted closure may not capture live linear
resources.

Lean declarations are concentrated in:

- `QLambda/Linear/Syntax.lean`;
- `QLambda/Linear/Context.lean`;
- `QLambda/Linear/Typing.lean`;
- `QLambda/Linear/TypeFormation.lean`.

The executable type checker is connected to the proof-level typing relation.
Negative examples include cloning a qubit and capturing a live qubit in an
unrestricted function.

### 2.2 Substitution and source safety

The formal substitution proof distinguishes used and unused linear variables.
It includes split rotation, all-`none` transport, linear substitution, and
unrestricted substitution with empty linear support.  These results imply
preservation for deterministic source reduction and for measurement-labelled
transitions.

For closed nonrecursive terms, progress yields either a value, a classical
step, or a genuine quantum blocking point.  It is not the vacuous statement
that a primitive is “stuck.”

---

## 3. Finite Quantum Runtime

A runtime configuration contains a finite register state, allocated-wire
information, an environment, and a typed control stack.  Gates act by their
canonical matrices.  Reset discards and reinitializes one wire.  Measurement
has two labelled branches whose weights are obtained from the Born rule.

The runtime proves:

- internal-transition preservation;
- measurement-transition preservation;
- nonnegativity and upper bounds of branch probabilities;
- normalization of the two measurement outcomes;
- progress modulo finite-wire exhaustion.

The runtime does not add source-level probability.  Probabilities label
physical measurement transitions only.

---

## 4. Quantum Sets, Relations, and qCPOs

A quantum set $X$ is a family of finite-dimensional Hilbert spaces
$(X_x)_{x\in\operatorname{At}(X)}$.  A quantum relation $R:X\to Y$ assigns to
each pair $(x,y)$ a complex linear subspace

$$
R(x,y)\subseteq \mathcal L(X_x,Y_y).
$$

Relations are ordered pointwise by inclusion.  Composition takes the span of
operator products over intermediate atoms, and dagger takes adjoints while
reversing atom pairs.

### 4.1 Formalized relation algebra

`QLambda/Domain/QuantumRel.lean` proves:

$$
(T\circ S)\circ R=T\circ(S\circ R),\qquad
R\circ 1=R=1\circ R,
$$

$$
(S\circ R)^\dagger=R^\dagger\circ S^\dagger,
$$

and

$$
\left(\bigvee_n S_n\right)\circ R
 =\bigvee_n(S_n\circ R),\qquad
S\circ\left(\bigvee_n R_n\right)
 =\bigvee_n(S\circ R_n).
$$

Each hom is a complete lattice.  Consequently quantum sets and quantum
relations form an $\omega$CPO-enriched category `qRelCategory`.

A relation is a quantum function when it satisfies the usual dagger
inequalities.  Comparable quantum functions are equal, and quantum functions
are closed under composition.  Unitary matrices yield quantum functions, and
the formalized $H$, $X$, $T$, $RY$, and $CX$ matrices agree with their
completed-CP presentations.

### 4.2 Quantum posets and completeness

A quantum poset is a quantum set with a reflexive, transitive, antisymmetric
quantum relation.  The qCPO condition is stated using increasing sequences of
functions from atomic probes.  Discrete quantum posets are qCPOs because
comparability forces equality, so every such chain is constant.  This gives
the qubit, classical bit, and tensor-unit objects used by the finite fragment.

`QuantumMonoidal.lean` supplies tensor on homs, internal hom, evaluation,
currying, unitors, associator, and braiding, and proves the required
$\omega$-supremum laws.  `QuantumLNL.lean` packages the resulting concrete
model.  Its nonlinear category consists of sets and functions with discrete
hom orders; classical inclusion is the graph functor and its right adjoint is
the set of relations from the tensor unit.  This deliberately avoids the
non-monotone graph map from pointwise-ordered continuous-function homs.

Separately, `QuantumCPOCategory.lean` packages quantum CPOs and
Scott-continuous quantum functions as an $\omega$CPO-enriched category.  The
formalization does not identify that category with the linear category of the
concrete `Set`--`qRel` adjunction. The published recursive LNL route instead
uses the quantum lift monad and its Kleisli category; that construction is not
yet present here.

---

## 5. Type-Indexed Denotation and Recursive Types

The semantic interface assigns:

$$
\llbracket\Gamma;\Delta\rrbracket
 =F\llbracket\Gamma\rrbracket\otimes\llbracket\Delta\rrbracket.
$$

Tensor and arrows are interpreted by the monoidal and closed structure.
Primitives carry presentation-independent finite CP classes.
Measurement is a finite instrument into a classical sum.

For a strictly positive recursive body $A(\alpha)$, the intended object
$\llbracket\mu\alpha.A\rrbracket$ is the bilimit of its finite unfolding
chain.  `QLambda/Domain/RecursiveTypes.lean` constructs the carrier of
compatible approximants and its complete-lattice structure.  Dropping and
restoring the zeroth approximation define inverse $\omega$-continuous maps,
packaged as `ProjectionChain.shiftIso`.

`QLambda/Linear/Denotation.lean` records the exact operations needed by every
typing rule, its constructor equations, and presentation-independent finite
CP meanings for physical primitives.  Classical beta, fix unfolding, and
fold/unfold are exact in the operational quotient.  We do not conflate that
interface with a fully instantiated qCPO denotation or claim unrestricted
adequacy: connecting every admissible source-type functor and every primitive
to one higher-order qCPO model remains outside the theorem boundary.

---

## 6. Deterministic Staging to Circuits

The circuit-normal fragment has statically bounded qubit and classical
registers.  A prefix allocator produces `Fin q` wire indices and proves
freshness, distinctness, and bounds.  Fresh-qubit allocation lowers to reset
on a fresh physical wire.

Staging is a fuelled call-by-value evaluator.  Lambdas, including
higher-order gate combinators, execute at staging time.  A successful result
contains first-order data only.  Recursive types and general recursion remain
in the language semantics but are excluded from this finite compilation
fragment.

Lean proves successful staging is deterministic and preserves source type,
resource typing, circuit well-formedness, and allocation bounds.  Regression
examples include Bell preparation, measurement-controlled gates, reset/reuse,
and higher-order gate composition.

---

## 7. Circuit Reflection and Completeness

`QLambda/Linear/Circuit.lean` translates between the circuit normal form and
the supported Composer block fragment.  Compilation preserves ideal CQ
denotation.  Reflection is total on a proof-carrying supported block, and
compilation after reflection returns the original block.

A canonical lambda quotation uses unrestricted binders for classical slots
and linear binders for wires.  `QuotationGeneral.lean` covers two qubit and
two classical registers, including distinct-wire $CX$, measurement,
reset/reuse, store, sequencing, conditionals, and bounded repeat.  It excludes
the unsupported coin command by an explicit `Quotable` predicate.

The checked capstones have the following meanings:

- `denote_compile`: staging and compilation preserve source denotation;
- `denote_reflect`: quotation preserves circuit denotation;
- `compile_reflect`: compiling a canonical representative returns the
  canonical circuit;
- `quotation_capstone`: every `Quotable` command has a well-typed canonical
  lambda representative whose compilation is the original command and whose
  inherited CQ denotation is equal to the circuit denotation.

---

## 8. Composer and OpenQASM Interchange

The target is a frozen, versioned AST with finite registers.  The supported
structured subset includes gates, measurement, reset, classical assignment,
conditionals, switches, bounded loops, boxes, and structured loop control
where the ideal semantics is defined.

Rendering produces canonical OpenQASM text.  Parsing accepts exactly the
declared canonical presentation and proves render/parse round trips under the
`ParserCanonical` boundary.  This is deliberately not a parser for arbitrary
OpenQASM 3 text.

Circuit denotation is an ideal classical--quantum instrument.  Sequencing is
instrument bind; measurement updates a classical slot; structured control is
interpreted compositionally.  Barriers and delays remain syntax but are
identities in the ideal semantics.

---

## 9. Mechanized Claims and Release Boundary

The following components are kernel checked without semantic axioms:

- source scope, typing, substitution, preservation, and progress;
- finite-register gate/reset/measurement runtime and normalization;
- pointed $\omega$CPO maps, products, evaluation, currying, and least fixed
  points;
- complete quantum-relation hom lattices and enriched composition;
- tensor/internal-hom closure and the concrete `Set`--`qRel` LNL model;
- the category of qCPOs and Scott-continuous quantum functions;
- inverse continuous shift maps for projection-chain bilimits;
- discrete qCPO instances and finite CP/gate presentations;
- deterministic staging with resource certificates;
- circuit/Composer correspondence on the supported block fragment;
- typed lambda quotation and circuit completeness for the declared two-wire
  fragment;
- structured canonical OpenQASM round trips.

The theorem boundary does not include an equivalence between the checked LNL
and qCPO categories, a fully instantiated denotation of every admissible
recursive source type, full abstraction, or unrestricted adequacy.  It also
does not include noisy-device behavior or exact finite synthesis of every
unitary.  Missing semantic structure is not introduced as an axiom or hidden
as a theorem parameter.

---

## 10. Related Work and Novelty Qualification

Weaver introduced quantum relations as operator subspaces.  Kornell,
Lindenhovius, and Mislove developed quantum posets and quantum CPOs and used
them for recursive quantum programming.  Selinger and Valiron established
linear/nonlinear semantic methods for higher-order quantum computation.
Pagani, Selinger, and Valiron gave quantitative semantics, and Tsukada and
Asada developed enriched presheaf models with strong recursion and
full-abstraction results.

Those works are the semantic foundation and prove stronger paper-level
results than claimed here: complete relation homs, arbitrary-join-preserving
composition, dagger compactness, quantum-function order, qCPO enrichment, and
the lifted recursive LNL model all have explicit literature support. Our
novelty claim is therefore limited to Lean formalization of the selected
representation and its integration with the typed source and finite circuit
pipeline. We list exact declarations. Absence of another proof-assistant
implementation from the sources checked is not itself a mathematical priority
proof.

---

## References

- A. Kornell, B. Lindenhovius, and M. Mislove, *Quantum CPOs*, 2021,
  arXiv:2109.02196.
- N. Weaver, *Quantum relations*, Memoirs of the American Mathematical
  Society 215(1010), 2012.
- A. Jenča and B. Lindenhovius, *Monoidal Quantaloids*, 2025.
- A. Kornell et al., *A Category of Quantum Posets*, 2023.
- A. Kornell et al., *Categories of Quantum CPOs*, arXiv:2406.01816.
- P. Selinger and B. Valiron, *A lambda calculus for quantum computation with
  classical control*, Mathematical Structures in Computer Science 16(3),
  2006.
- M. Pagani, P. Selinger, and B. Valiron, *Applying quantitative semantics to
  higher-order quantum computing*, POPL, 2014.
- T. Tsukada and K. Asada, *Enriched presheaf model of quantum FPC*, 2024.

---

Lean was produced with AI-agent assistance under the author's direction and
review.  The trusted proof object is the Lean kernel output, not generated
prose or tests.
