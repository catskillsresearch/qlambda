# Provenance

This repository is an original Lean 4 development by Lars Warren Ericson of
a typed linear/nonlinear quantum lambda calculus, quantum-relation and
quantum-CPO infrastructure, and finite circuit interchange.

## Mathematical sources

- Weaver, *Quantum relations* (2012): operator-subspace presentation of
  quantum relations.
- Kornell, Lindenhovius, and Mislove, *Quantum CPOs* (2021): quantum posets,
  quantum functions, and quantum CPO continuity.
- Jenča and Lindenhovius, *Monoidal Quantaloids* (2025): complete
  relation-hom lattices, arbitrary-join-preserving composition, and dagger
  compactness.
- Kornell, Lindenhovius, and Mislove, *A Category of Quantum Posets* (2023)
  and *Categories of Quantum CPOs* (2026): function order, explicit qCPO
  limits, and the lifted Kleisli LNL construction.
- Selinger and Valiron, *A linear-non-linear model for a quantum lambda
  calculus* (2009): LNL semantic architecture.
- Smyth and Plotkin, *The category-theoretic solution of recursive domain
  equations* (1982): projection-chain and bilimit method.

`docs/NOVELTY_AUDIT.md` records the focused source check supporting the
qualified novelty language in `arxiv.md`.

## Original formal proofs

The repository supplies the selected matrix/subspace representation and Lean
proofs of quantum-relation composition, dagger, complete hom orders,
countable-join preservation, compact closure, the concrete `Set ⊣ qRel`
adjunction, the Scott-function qCPO category, continuous projection-chain
shift isomorphisms, deterministic staging, canonical two-wire lambda
quotation, and structured OpenQASM round trips.

These are claimed as novel formal proofs. Mathematical priority is asserted
only where `arxiv.md` says “to our knowledge” and is limited by the documented
literature search.

The checked `Set ⊣ qRel` declaration is not identified with the published
lifted-qCPO recursive model. See `docs/QCPO_LNL_DESIGN.md`.

## Vendored material and automation

`vendor/scott1972` is a frozen same-author Lean development of Scott's
*Continuous Lattices*, identified by `vendor/FROZEN.txt`. It is retained for
preservation and background order theory; the compared typed-linear
statements do not import the retired omega-QVA architecture.

AI agents assisted with proof exploration, refactoring, tests, and prose
under author direction. Lean kernel checking, not generated text, is the
proof authority.

## Palomar surface

`comparator.json` selects:

- `QLambda.Palomar.source_type_safety`;
- `QLambda.Palomar.quotation_capstone`.

`Challenge.lean` imports only Mathlib. It restates the source syntax, typing,
reduction, circuit normal form, and two-wire quotation verbatim and states
these results with explicit holes under the Palomar convention.
`Solution.lean` proves the same statements from `QLambda` without `sorry`.
