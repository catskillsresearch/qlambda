# Handoff — qlambda (ωQVA / quantum domain equation)

Palomar statement of record: `omegaQVA_quantum_domain_equation_solved`.
Narrative: `arxiv.md`. Metadata: `formalization.yaml`, `comparator.json`.
Vendor: `vendor/scott1972` (frozen SHA in `vendor/FROZEN.txt`).
CKL 2026 paper in `sources/`.

## Resume

1. Read this file and `PROVENANCE.md`.
2. `lake build QLambda Challenge Solution`
3. `bash scripts/compare_challenge_solution_types.sh`
4. Compared names must match between Challenge and Solution (`pp.all`).

## Status (2026-08-22)

Palomar packaging (Apache-2.0, Zenodo/arXiv scripts, Challenge /
Solution / comparator / formalization.yaml) is in place. `lake build`
typechecks `QLambda`, `Challenge`, and `Solution` under
`leanprover/lean4:v4.33.0`. Proof modules in `Quantum/` and
`QuantumStateSpace.lean` are sorry-free. `Challenge.lean` may `sorry`.
`bash scripts/compare_challenge_solution_types.sh` reports a type match.
