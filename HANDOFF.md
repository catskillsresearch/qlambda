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
unfolding, general capture-avoiding value substitution, ordinary and
recursive semantic β-equations, and α-invariance for ordinary and recursive
binders are proved without `sorry`.

Unweighted internal reduction is sound: `Step M N` implies
`interp N ρ ≤ interp M ρ`, and the result lifts to `Reduces`. External
selection and weighted branches now have separate abstract specifications;
top-level external and probabilistic branch theorems preserve their Boolean
label and probability respectively. Full abstract `WeightedStep` soundness is
proved under explicit application-closure laws. TT internal choice is
implemented as pointwise join and is exactly preserved by continuation bind.
Concrete qubit return, Pauli-X, and Z-measurement primitives are embedded into
the two-dimensional TT model.

## Surviving roadmap

The remaining language-semantics goals are:

1. construct a weighted TT result aggregation (the TT result lattice has no
   canonical convex operation), prove Scott continuity, and use it for
   probabilistic choice without identifying probability with lattice join;
2. construct an environment-indexed external-choice representation and
   Boolean selectors without identifying external choice with internal
   nondeterminism;
3. combine those operations with the existing TT internal choice to register
   a lawful `HasComputationChoice` instance;
4. instantiate the weighted application-context closure laws for that
   concrete TT construction, then formulate and prove adequacy for a
   separating observation relation.

For stronger embedding claims, a density theorem for
`CodedTestRepresentation` and a concrete directed-supremum non-closure
witness remain separate optional obligations.
