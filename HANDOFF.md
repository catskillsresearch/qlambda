# Handoff — typed linear qlambda

The active repository is the typed linear redesign. The retired untyped
omega-QVA, choice/continuation, scratch-lowering, and hardware-adequacy source
trees have been removed.

## Entry points

- Paper: `arxiv.md`
- Theorem index: `THEOREMS.md`
- Root import: `QLambda.lean`
- Palomar statements/proofs: `Challenge.lean`, `Solution.lean`
- Comparator metadata: `comparator.json`, `formalization.yaml`
- Novelty evidence: `docs/NOVELTY_AUDIT.md`

The compared declarations are:

- `QLambda.Palomar.quantum_lnl_model`
- `QLambda.Palomar.quantum_cpo_enriched_category`
- `QLambda.Palomar.two_wire_circuit_completeness`

## Verification

```bash
lake build
lake env lean Challenge.lean
lake env lean Solution.lean
bash scripts/palomar_preflight.sh --mechanical-only
bash scripts/build_arxiv_pdf.sh
bash scripts/package_zenodo.sh
```

`Challenge.lean` is the only intended location for theorem holes.
`Solution.lean` and the `QLambda/` implementation must remain sorry-free.

## Scope

The concrete LNL instance is the ordinary `Set ⊣ qRel` model. A separate
category packages quantum CPOs and Scott-continuous quantum functions. The
repository does not claim those categories equivalent.

Circuit completeness is for the declared canonical two-wire finite fragment:
single-wire gates, distinct-wire CX, reset, measurement, store, sequencing,
conditionals, and bounded repeat. OpenQASM is an ideal interchange format,
not a noisy-backend or arbitrary-Qiskit semantics.

The generic `DenotationModel` remains an explicit interface for compositional
source denotation. The checked source equations additionally have an exact
operational quotient. The release does not claim full abstraction or
unrestricted adequacy for every recursive term.
