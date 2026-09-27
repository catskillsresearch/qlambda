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

The pin is `leanprover/lean4:v4.35.0-rc3` in `lean-toolchain` and `lakefile.toml`.

The compared declarations are the `QLambda.Palomar` theorems in
`comparator.json`. `arxiv.md` states those same types and the Solution
values of the definition holes.

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

`Command.GeneralQuotation.Quotation.quotation_capstone` adds ideal CQ equality
and is not compared.

`Challenge.lean` imports only Mathlib and restates the supporting definitions
verbatim. Comparator compares their elaborated constants, including
auxiliary match functions, so edits to `QLambda/Linear/Syntax.lean`,
`TypeFormation.lean`, `Context.lean`, `Typing.lean`, `Substitution.lean`,
`Operational.lean`, `Circuit.lean`, `Composer/Syntax.lean`, or the public
quotation definitions in `QuotationGeneral.lean` must be mirrored there.

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
and conditionals. OpenQASM is an ideal interchange format,
not a noisy-backend or arbitrary-Qiskit semantics.

The generic `DenotationModel` remains an explicit interface for compositional
source denotation, not an instance. The checked source equations additionally
have an exact operational quotient, not a semantic soundness result.
`Quotation.denote` is inherited from its represented command. The selected
completion objective is a typed CP-enriched presheaf submodel, concrete
source denotation, first-order-observable adequacy, and a source-level staging
theorem. The release does not claim those results, full abstraction, or
unrestricted adequacy for every recursive term.
