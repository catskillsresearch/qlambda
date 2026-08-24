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

## Status (2026-08-23)

Palomar packaging (Apache-2.0, Zenodo/arXiv scripts, Challenge /
Solution / comparator / formalization.yaml) is in place. `lake build`
typechecks `QLambda`, `Challenge`, and `Solution` under
`leanprover/lean4:v4.33.0`. Proof modules in `QLambda/` are
sorry-free where previously discharged. `Challenge.lean` may `sorry`.
`bash scripts/compare_challenge_solution_types.sh` reports a type match.

The domain construction now includes the concrete fixed-register
`TTContinuation.model`, its lawful continuation monad, and
`TTPhysicalEmbedding.embed` for finite TNI CP instruments. Exact return,
finitely presented map/bind compatibility, represented-test refinement
recovery, and the directed-supremum obstruction to a finite-image Scott
retract are proved.

The computation-valued core is also implemented. `Term Prim` and the
operational relations support closed primitives and recursive abstractions.
`QLambda.interp` denotes every term in `Q(D∞)`: values use monadic `unit`,
application uses Scott-continuous bind, and recursion uses Scott `fix`.
Environment continuity, constructor equations, value purity, recursive
unfolding, and the pure semantic β-equation are proved without `sorry`.

## Surviving roadmap

The remaining language-semantics goals are:

1. prove the remaining renaming, weakening, and capture-avoiding
   substitution correspondence for `QLambda.interp`;
2. prove soundness for the existing small-step interfaces, then adequacy;
3. construct concrete probabilistic, internal, and external choice operations on
   `TTContinuationPower` and prove their laws and finite-instrument
   compatibility.

For stronger embedding claims, a density theorem for
`CodedTestRepresentation` and a concrete directed-supremum non-closure
witness remain separate optional obligations.
