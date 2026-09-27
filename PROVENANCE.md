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

These are Lean proofs of the selected representation. No priority among
formalizations is claimed; a search for other proof-assistant formalizations
has not been completed.

The checked `Set ⊣ qRel` declaration is not identified with the published
lifted-qCPO recursive model. See `docs/QCPO_LNL_DESIGN.md`.

## Vendored material and automation

No Lean foundation libraries are currently vendored under `vendor/`. Palomar
policy pins live in `vendor/PALOMAR_POLICY_PIN` and
`vendor/PALOMAR_PREFLIGHT_PIN`.

AI agents assisted with proof exploration, refactoring, tests, and prose
under author direction. Lean kernel checking, not generated text, is the
proof authority.

## Palomar surface

`comparator.json` selects:

- `QLambda.Palomar.source_type_safety`
- `QLambda.Palomar.quotation_capstone`
- `QLambda.Palomar.runtime_born_normalizes`
- `QLambda.Palomar.runtime_internal_preservation`
- `QLambda.Palomar.runtime_measurement_preservation`
- `QLambda.Palomar.runtime_progress`
- `QLambda.Palomar.quantumRel_assoc`
- `QLambda.Palomar.quantumRel_dagger_comp`
- `QLambda.Palomar.quantumRel_comp_iSup_left`
- `QLambda.Palomar.quantumRel_comp_iSup_right`
- `QLambda.Palomar.quantumRel_id_comp`
- `QLambda.Palomar.quantumRel_comp_id`
- `QLambda.Palomar.qubit_isQuantumCPO`
- `QLambda.Palomar.set_qRel_linear_objects`
- `QLambda.Palomar.qCPO_category_objects`
- `QLambda.Palomar.shift_forward_backward`
- `QLambda.Palomar.shift_backward_forward`
- `QLambda.Palomar.prim_cp_agreement`
- `QLambda.Palomar.cx_cp_agreement`
- `QLambda.Palomar.measure_elim_denotation`
- `QLambda.Palomar.staging_deterministic`
- `QLambda.Palomar.staging_well_formed`
- `QLambda.Palomar.staging_compile_agreement`
- `QLambda.Palomar.openqasm_render_roundTrip`
- `QLambda.Palomar.openqasm_export_roundTrip`
- `QLambda.Palomar.measured_new0_born_false`
- `QLambda.Palomar.measured_new0_born_true`
- `QLambda.Palomar.measured_new0_within_bound`
- `QLambda.Palomar.measure_branch_agrees`

`Challenge.lean` imports only Mathlib. It restates the source syntax, typing,
reduction, circuit normal form, and two-wire quotation verbatim. The runtime,
relation, presheaf, staging, and OpenQASM carriers are definition holes.
`QLambda.Palomar.quotation_capstone` is typing plus compile reflection.
`Command.GeneralQuotation.Quotation.quotation_capstone` adds ideal CQ
equality and is kernel-checked in the library, not selected.
`Solution.lean` proves the compared statements from `QLambda` without `sorry`.
