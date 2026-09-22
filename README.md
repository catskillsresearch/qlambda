[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/qlambda/build.yml?label=Lean%204)](https://github.com/catskillsresearch/qlambda/actions/workflows/build.yml)

# qlambda

Lean 4 formalization of a typed linear/nonlinear quantum lambda calculus,
quantum-relation/qCPO semantics, and a verified finite circuit interchange.

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
- `QLambda/Linear/RegFile.lean`, `Elaboration.lean`: deterministic,
  resource-certified staging of a terminating first-order fragment.
- `QLambda/Linear/Circuit.lean`, `Quotation.lean`,
  `QuotationGeneral.lean`: circuit normal form, Composer reflection, and
  canonical typed quotation for the declared two-wire fragment.
- `QLambda/Composer/OpenQASMParser.lean`: canonical structured OpenQASM
  parse/render round trips.

## Checked boundary

The active root and Palomar surface now expose the typed redesign only.  The
concrete LNL model, quantum-CPO category, projection-chain shift isomorphism,
runtime, staging, two-wire quotation capstone, and OpenQASM round trips all
compile without implementation `sorry`.

`DenotationModel` remains the explicit interface for a compositional source
interpretation; the source equations also have an exact operational quotient.
This release does not claim an equivalence between the `Set ⊣ qRel` model and
the Scott-function qCPO category, full abstraction, or unrestricted adequacy
for arbitrary recursive programs. `docs/NOVELTY_AUDIT.md` records the
distinction between published mathematics and new Lean proofs.
`docs/QCPO_LNL_DESIGN.md` records the published lifted-qCPO Kleisli route and
the remaining obstruction for allocation, reset, and arbitrary CP
instruments.

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

Mechanical Palomar checks:

```bash
bash scripts/palomar_preflight.sh --mechanical-only
```

Before a release candidate:

```bash
bash scripts/palomar_preflight.sh
bash scripts/build_arxiv_pdf.sh
bash scripts/package_zenodo.sh
```

## Provenance

The development uses Mathlib and the vendored
[`scott1972`](https://github.com/catskillsresearch/scott1972) formalization.
The quantum-set/qCPO construction follows Weaver and
Kornell--Lindenhovius--Mislove.  See `PROVENANCE.md` and the paper references.

AI agents assisted with proof exploration, code, and prose under the author's
direction.  Lean kernel checking, not generated text, is the proof authority.
