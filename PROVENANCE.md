# Provenance

This Palomar snapshot is the quantum-domain companion to
[`scott1972`](https://github.com/catskillsresearch/scott1972)
(Lean 4 mechanization of Dana Scott, *Continuous Lattices*, LNM 274).
The 1972 library is copied into `vendor/scott1972` at the frozen SHA in
`vendor/FROZEN.txt` so a preservation fork of `qlambda` contains the
complete development. The remote remains the 1972 home.

## Palomar entry

The Comparator configuration `comparator.json` selects one theorem:

`Scott1972.ContinuousLattice.canonical_omegaQVA_quantum_domain_equation_solved`

Challenge.lean states the capstone and its Mathlib type surface; Solution.lean
imports the sorry-free proof from `QLambda/QuantumDomainEquation.lean`.
The selected theorem constructs the canonical one-point base and stage-zero
projection pair for every `QuantumPowerModel`. The original general theorem
with supplied `(D₀, j₀)`, the concrete `TTContinuation.model` specialization,
supporting project results, and hardware capstones are documented in
`formalization.yaml`, `THEOREMS.md`, and `arxiv.md` but are outside this
Comparator selection.

Local readiness:

```bash
bash scripts/palomar_preflight.sh --mechanical-only   # CI
bash scripts/palomar_preflight.sh                       # before submission
```

Registry submission is a separate step at
[submit.palomar-registry.org](https://submit.palomar-registry.org/) and
requires a pinned GitHub commit plus explicit consent after Palomar's
mechanical and editorial checks.

Packaging pattern reference: [`scott_models`](https://github.com/catskillsresearch/scott_models).

## Author work

The ω**QVA** type surface, Loewner state space, saturation flattening
used for the quantum bilimit, and the capstone
`canonical_omegaQVA_quantum_domain_equation_solved` are original Lean of
Lars Warren Ericson (Catskills Research Company, 2026). They extend
Scott 1972 inverse limits (`embInf`, `projInf`, Theorem 4.4) from
`D_∞ ≅ [D_∞ → D_∞]` to the quantum functor `[D → Q(D)]`.

## Literature used in the proofs

Chen, Kou, and Lyu, *Finite-valuation approximable structures*
(arXiv:2608.03073, 2026) supply the classical saturation pattern
(v1 Lemmas 6.5–6.7). The paper is in `sources/`. The lemmas are
mechanized in `QLambda/Saturation.lean`.

## Related remotes

| Remote | Role |
| --- | --- |
| [`scott1972`](https://github.com/catskillsresearch/scott1972) | Continuous lattices; Theorem 4.4 (vendored) |
| [`scott_models`](https://github.com/catskillsresearch/scott_models) | Palomar packaging pattern; presentation bridges |
| arXiv:2608.03073 | Chen–Kou–Lyu ω**FVA** / Jung–Tix (`sources/`) |
