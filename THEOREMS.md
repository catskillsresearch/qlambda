# Principal theorem index

This is a compact index of the proved Lean surface. `arxiv.md` is the
narrative status of record. Names below are Lean declarations, not claims
about the motivating literature or a Qiskit compiler.

## Quantum domain

- `Scott1972.ContinuousLattice.canonical_omegaQVA_quantum_domain_equation_solved`
  — `QLambda/QuantumDomainEquation.lean`; the Palomar theorem of record. For
  every bundled `QuantumPowerModel`, the canonical one-point tower has an
  `omegaQVA` inverse limit, exact mutually inverse limit maps, an order
  isomorphism with `[D_infinity -> Q(D_infinity)]`, and Scott's bilimit
  identity.
- `Scott1972.ContinuousLattice.omegaQVA_quantum_domain_equation_solved`
  — `QLambda/QuantumDomainEquation.lean`. The more general theorem takes an
  initial `QDomain D₀` and a supplied embedding–retraction pair `j₀`; its
  bonding retraction has direction `[D₀ -> Q(D₀)] ↠ D₀`.
- `QLambda.TTContinuation.canonical_omegaQVA_quantum_domain_equation_solved`
  — `QLambda/TTContinuationDomainEquation.lean`. The canonical result
  specialized to the concrete fixed-register continuation model.
- `Scott1972.ContinuousLattice.qDInf_isOmegaQVA`
  — `QLambda/QuantumDomainEquation.lean`. The inverse limit is an
  `omegaQVA`, by the retract-of-countable-product construction.
- `Scott1972.ContinuousLattice.finitelySeparated_wayBelow`
  — `QLambda/Saturation.lean`. A finitely separated Scott map satisfies
  `f x << x`.
- `Scott1972.ContinuousLattice.omegaQVA_closed_under_functionSpace`
  — `QLambda/QuantumPower.lean`. Function spaces preserve `omegaQVA`.

Boundary: these theorems formalize the quantum `omegaQVA` construction and
the parameterized quantum domain equation. They do not formalize the full
classical Chen–Kou–Lyu `omegaFVA` development or independently re-prove the
Jung–Tix result.

## Token theories and physical embedding

- `QLambda.finitaryTTRefines_iff_token_holds`
  — `QLambda/TTRefinement.lean`. Finitary TT refinement is characterized by
  preservation of all finite strict tokens.
- `QLambda.ttTokenTheory_isContinuousLattice` and
  `QLambda.satisfiedTTTheory_le_iff_finitaryTTRefines`
  — `QLambda/TTRoundedTheory.lean`. The token completion is a continuous
  lattice and its order exactly captures finitary TT refinement.
- `QLambda.TTPhysicalEmbedding.embed_unit`,
  `QLambda.TTPhysicalEmbedding.embed_map_satisfied`, and
  `QLambda.TTPhysicalEmbedding.embed_bind_satisfied`
  — `QLambda/TTPhysicalEmbedding.lean`. Return is preserved exactly; map and
  bind agree on finitely presented result continuations.
- `QLambda.TTPhysicalEmbedding.finitaryTTRefines_of_embed_le`
  — `QLambda/TTPhysicalEmbedding.lean`. Embedding order implies finitary TT
  refinement, using the proved representation of every rational coded test.
- `QLambda.no_finiteImageScottRetraction_dyadic`
  — `QLambda/FiniteImageNonclosure.lean`. A concrete directed dyadic chain
  rules out a Scott retraction onto the finite embedded image.

Boundary: finite instruments embed into a larger continuation model. The
results do not identify that carrier with finite instruments, and do not
claim that raw `InstrumentPower` is an `omegaQVA`.

## Language semantics

- `QLambda.interp_continuous`, `QLambda.interp_value`, and
  `QLambda.recLambdaValue_unfold` — `QLambda/Interp.lean`. Terms have a
  compositional Scott-continuous call-by-value interpretation; values are
  pure computations and recursive abstractions satisfy the fixed-point
  unfolding equation.
- `QLambda.interp_step_le` and `QLambda.interp_reduces_le`
  — `QLambda/Soundness.lean`. The unweighted operational relations are
  sound in the denotational order.

Boundary: probabilistic, internal, and external choice are distinct
operations in the concrete TT continuation model. This is not a Qiskit
compiler or a formal Qiskit equivalence theorem.

## Hardware channel-tree completeness

- `QLambda.HardwareChannelSemantics.closed_term_presented_channelTreeCompleteness_of_productive_case`
  and
  `QLambda.HardwareChannelSemantics.closed_term_presented_token_adequacy_of_productive_case`
  — `QLambda/HardwareChannel/Productive.lean`. These cover
  `ProductiveClosedCase`, including the explicitly restricted ordinary and
  recursive lambda applications whose argument is an `extern`.
- `QLambda.HardwareChannelSemantics.closed_stuck_free_presented_channelTreeCompleteness`
  and
  `QLambda.HardwareChannelSemantics.closed_stuck_free_presented_token_adequacy`
  — `QLambda/HardwareChannel/Coverage.lean`. These are the final consolidated
  capstones for programs carrying a `ClosedStuckFreeCoverage` witness.

`ClosedStuckFreeCoverage` is the exact boundary. Its constructors cover
closed `NoApp`, `FunAppFrag`, `Produces 0`, `ProductiveClosedCase` with
`MeasureDistinct`, and `RestrictedExternApplication`. The last class is
limited to
`app (lam x body) (extern left right)` and
`app (recLam self x body) (extern left right)` with the stated `NoApp`,
`AdminNoApp`, and `Atomic` hypotheses; its direct theorem does not require
`MeasureDistinct`.

The token capstone is presented adequacy: it quantifies over a continuation
represented by a finite instrument and characterizes selected TT tokens by
a realized finite channel tree. It is not an unrestricted theorem for every
closed source term, arbitrary stuck application, or arbitrary Scott
continuation.

## External context

Chen–Kou–Lyu `omegaFVA` and the Jung–Tix problem motivate the finite
separation and saturation pattern; they are literature, not a Lean
dependency and not formalized here in full. The Qiskit tables in `arxiv.md`
are operational motivation through shared CP denotations, not verified
compiler correctness or a formal back-and-forth theorem.
