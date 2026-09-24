[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/qlambda/build.yml?label=Lean%204)](https://github.com/catskillsresearch/qlambda/actions/workflows/build.yml)

# qlambda

Lean 4 formalization of a typed linear/nonlinear quantum lambda calculus,
quantum-relation and qCPO foundations, and a verified $N$-bounded first-order
fragment with Route A presheaf denotation, Composer/OpenQASM staging, and
two-wire quotation completeness.  Full-language bang/LNL denotation remains an
explicit objective behind AmbientCP Day-bang glue.

The source judgment

```text
Γ ; Δ ⊢ M : A
```

separates unrestricted classical assumptions from exactly-once linear
assumptions.  The language has linear and unrestricted functions, tensors,
classical bits, qubits, recursive types, allocation, gates, reset, and
measurement.  Probability arises only from measurement.  There is no source
`emit`, probabilistic choice, internal choice, or external choice.

## Current formalized layers

- `QLambda/Linear/Syntax.lean`, `Typing.lean`, `Metatheory.lean`:
  scope, verified type inference, substitution, preservation, and source
  progress.
- `QLambda/Linear/Runtime.lean`: finite quantum registers, gate/reset/
  measurement transitions, preservation, progress, and measurement
  normalization.
- `QLambda/Domain/OmegaCPO.lean`, `Enriched.lean`,
  `LinearNonlinear.lean`: omega-complete orders, continuous maps,
  enriched-category interfaces, and fixed points on pointed objects.
- `QLambda/Domain/QuantumSet.lean`, `QuantumRel.lean`,
  `QuantumRelational.lean`, `QuantumMonoidal.lean`, `QuantumLNL.lean`:
  quantum sets, complete-lattice relation homs,
  dagger/category laws, the published pointwise order on quantum functions,
  compact closure, the concrete `Set ⊣ qRel` LNL model, discrete qCPOs, and
  finite gate embeddings.
- `QLambda/Domain/QuantumCPOCategory.lean`, `RecursiveTypes.lean`: the
  Scott-continuous quantum-function category and continuous projection-chain
  shift/fold isomorphisms.
- `QLambda/Domain/Presheaf/`: intrinsic Choi CP maps, TNI superoperators,
  specialized modules, Yoneda, representable Day tensor/internal hom, finite
  symmetric powers, the Day bang comonoid and cofree UP for dimensions
  `A ≤ 1`, and kernel-checked TNI / Route A obstructions at fiber dimension
  `2`.  This is the substrate for the remaining CP-enriched source
  denotation, not that denotation.
- `QLambda/Linear/RegFile.lean`, `Elaboration.lean`: deterministic,
  resource-certified staging of a terminating first-order fragment.
- `QLambda/Linear/Circuit.lean`, `Quotation.lean`,
  `QuotationGeneral.lean`: circuit normal form, Composer reflection, and
  canonical typed quotation for the declared two-wire fragment.
- `QLambda/Composer/OpenQASMParser.lean`: canonical structured OpenQASM
  parse/render round trips.

## Checked boundary

The active root exposes the typed redesign only.  The ordinary
`Set ⊣ qRel` LNL model, quantum-CPO category, generic projection-chain shift
isomorphism, runtime, staging, two-wire quotation capstone, and OpenQASM
round trips all compile without implementation `sorry`.

`DenotationModel` remains the explicit interface for a compositional source
interpretation, not an instantiated semantics.  `ProjectionChain.shiftIso`
does not yet interpret source `mu`, and quotation CQ equality is inherited
from the represented command rather than proved from source denotation.

The semantic objective is a typed submodel of the CP-enriched
superoperator-module presheaf semantics.  For `A ≤ 1` the exponential now
satisfies `ComonoidHom(C, !A) ≃ Hom(C, y(A))` with Day comultiplication and
co-Kleisli promotion.  At the same time, generic joint TNI precomposition at
fiber dimension `d ≥ 2` is false, and the raw canonical bang-split
joint-effect bound (Route A) is refuted at `A = 2`.
`BangSplitEffectAdmissible` is that global universal bound (not a hereditary
carrier-membership predicate) and fails by excluding the degree-one identity
series.  Scaling by `1/2` repairs the `(2,1)` matrix inequality, but
left/right counit force the `(0,1)`/`(1,0)` boundary weights to remain `1`,
so half-scaling is not a counital repair.  Any
`BangComultDayTransferWitness` would kernel-checkably refute
`BangComultComponentsAdmissible 2`, but no TNI/representable witness is
constructed.  L8 instead publishes the ambient-CP replacement
`AmbientCPDayBangCategory` with Gate-8 suite `ambientCP_gate8_testSuite`
(terminal `day_bang_l8_resolved_by_ambientCP_replacement`).  An
all-dimensional TNI cofree bang, general Day closure on based modules, a
premise-free `presheafQuantumLNL`, and full-language adequacy remain
objectives (Track L waits on an AmbientCP comonoid).  The **minimum fragment**
(first-order data, linear arrows with first-order domain, unrestricted bit
binders, primitives, measurement; no `mu`/`fix`) has a Route A
`PresheafFragmentModel`, compositional `FragCert.denote` via controlled
`iteElim`, classical-bit comonoid contexts with Day/FO closed β/η, closed FO
`ite` and closed linear/unrestricted identity β, closed `unpair` β, constant
unrestricted subst β, Step congruence / complete fragment Step package,
measured `new0` Born adequacy (`FragmentMeasuredSimulation`), N-qubit
denotation + OpenQASM staging packaging
(`n_qubit_fragment_denotation_openqasm_interface`), Hom-side quote spines, and
spine-driven CQ bridges for skip/x/h plus a covering set
(t/reset/measure/seq-skip; branch via packaging) — see
`QLambda/Linear/SemanticFragment.lean`, `FragmentModel.lean`,
`FragmentDenotation.lean`, `FragmentIte.lean`, `FragmentContext.lean`,
`FragmentAdequacy.lean`, `FragmentCoherence.lean`, `FragmentRuntimeN.lean`,
`FragmentSourceCircuitN.lean`, `FragmentQuoteBridgeExt.lean`,
`FragmentNDenotation.lean`.  The proposed copy/discard on physical
`representable 2` is formally not counital; `classicalBitModule` supplies
the unrestricted carrier with a checked Day comonoid.  Remaining Quotable
Hom spines beyond that covering set, and undecidable arbitrary Hom→CQ
extract, remain open.  Track L is deferred on L9→L10 glue:
relative AmbientCP admissibility for `A ≤ 1`, a degree-row gate at 2, and
`AmbientCPComonoid` packaging for `A ≤ 1` are checked
(`day_bang_l9_ambientCP_bang_admissible`); A=1-style glue is blocked by
`¬ BangDegreeUnitRectangleHasSum 2`, so glued
`BangComultAmbientCPAdmissible 2` remains open.  This release does not
claim full abstraction or unrestricted higher-order adequacy.
`docs/NOVELTY_AUDIT.md` records the distinction between published mathematics
and new Lean proofs.

## Circuit and OpenQASM boundary

The circuit target is a frozen, versioned Composer/OpenQASM AST with ideal
classical--quantum instrument semantics.  It is not the Qiskit Python API and
does not model calibration, transpiler heuristics, device noise, or arbitrary
OpenQASM text.  “Circuit completeness” means representability of every
well-formed circuit in the declared supported fragment, not exact finite
synthesis of every unitary.

## Build

```bash
lake exe cache get
lake build
```

Mechanical Palomar checks (build, Comparator, sorry/axioms):

```bash
bash scripts/palomar_preflight.sh --mechanical-only
```

Palomar packaging pre-checks (deterministic metadata / `formalization.yaml`
alignment; no LLM editorial audit):

```bash
PALOMAR_PROJECT_ROOT=$PWD python3 ../palomar-preflight/palomar_editorial_checks.py
```

Before a Palomar / CMU-TR packaging candidate (still skip LLM editorial until ready):

```bash
bash scripts/palomar_preflight.sh --mechanical-only
PALOMAR_PROJECT_ROOT=$PWD python3 ../palomar-preflight/palomar_editorial_checks.py
bash scripts/build_arxiv_pdf.sh
```

The PDF uses CMU `cmu-titlepage2.sty` with table of contents and list of
figures; see `docs/CMU_TECH_REPORT.md`.

## Provenance

The development uses Mathlib and the vendored
[`scott1972`](https://github.com/catskillsresearch/scott1972) formalization.
The quantum-set/qCPO construction follows Weaver and
Kornell--Lindenhovius--Mislove.  See `PROVENANCE.md` and the paper references.

AI agents assisted with proof exploration, code, and prose under the author's
direction.  Lean kernel checking, not generated text, is the proof authority.
