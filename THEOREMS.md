# Typed linear qlambda theorem index

This index lists the active replacement theorem surface.

## Source language and runtime

- `QLambda.Linear.infer_sound`
- `QLambda.Linear.substLin_zero_preserves`
- `QLambda.Linear.substUnres_zero_preserves`
- `QLambda.Linear.step_preservation`
- `QLambda.Linear.measStep_preservation`
- `QLambda.Linear.step_deterministic`
- `QLambda.Linear.progress`
- `QLambda.Linear.Runtime.internal_preservation`
- `QLambda.Linear.Runtime.measurement_preservation`
- `QLambda.Linear.Runtime.progress`
- `QLambda.Linear.Runtime.measureProbability_false_add_true`

Probability labels measurement transitions; it is not a source term former.

## Omega-CPO foundations

- `QLambda.Domain.OmegaMap.fix_eq`
- `QLambda.Domain.OmegaMap.fix_le_of_prefixed`
- `QLambda.Domain.OmegaMap.paramFix_mono`
- `QLambda.Domain.omegaMapCategory`
- `QLambda.Domain.ProjectionChain.shiftForwardMap`
- `QLambda.Domain.ProjectionChain.shiftBackwardMap`
- `QLambda.Domain.ProjectionChain.shiftIso`

`OmegaComplete` does not imply pointedness. Least fixed points separately
require `OrderBot`.

## Quantum relations, closure, and LNL

- `QLambda.Domain.QuantumRel.dagger_dagger`
- `QLambda.Domain.QuantumRel.dagger_comp`
- `QLambda.Domain.QuantumRel.id_comp`
- `QLambda.Domain.QuantumRel.comp_id`
- `QLambda.Domain.QuantumRel.assoc`
- `QLambda.Domain.QuantumRel.comp_iSup_left`
- `QLambda.Domain.QuantumRel.comp_iSup_right`
- `QLambda.Domain.QuantumRel.IsFunction.comp`
- `QLambda.Domain.QuantumFunction.comp_dagger_le_order`
- `QLambda.Domain.QuantumRel.tensor_comp`
- `QLambda.Domain.QuantumRel.curry_uncurry`
- `QLambda.Domain.QuantumRel.uncurry_curry`
- `QLambda.Domain.qRelSymmetricMonoidalClosed`
- `QLambda.Domain.classicalToQRel`
- `QLambda.Domain.qRelStates`
- `QLambda.Domain.quantumLNL`

The nonlinear side uses discrete hom orders. This avoids the false claim that
ordinary graph relations are monotone from pointwise-ordered function homs.

## Quantum CPO category

- the `PartialOrder (QLambda.Domain.QuantumFunction P Q)` instance
- `QLambda.Domain.discrete_isQuantumCPO`
- `QLambda.Domain.ScottFunction.comp`
- `QLambda.Domain.ScottFunction.ofDiscreteDomain`
- `QLambda.Domain.qCPOCategory`

The qCPO category and the concrete `Set ⊣ qRel` LNL model are both checked;
no equivalence between them is claimed. The published recursive model uses a
quantum-lift Kleisli category, which is not yet constructed here.

## Finite quantum operations

- `QLambda.Domain.CompletedCP.ofKraus_eq_of_semEq`
- `QLambda.Domain.CompletedCP.ofKraus_comp_assoc`
- `QLambda.Domain.CompletedCP.measure_probability_normalization`
- `QLambda.Linear.Prim.completedCP`
- `QLambda.Linear.Prim.qubitMeasurement`

`CompletedCP` identifies Kraus presentations by intrinsic semantic
refinement. It is a first-order presentation, not the higher-order category.

## Source equations

- `QLambda.Linear.step_sound`
- `QLambda.Linear.betaL_exact`
- `QLambda.Linear.betaU_exact`
- `QLambda.Linear.unpair_exact`
- `QLambda.Linear.unfold_fold_exact`
- `QLambda.Linear.fix_exact`
- `QLambda.Linear.operational_quotient_exact`

`DenotationModel` gives the compositional categorical interface and
constructor equations. The exact operational quotient validates the listed
source equations. The repository does not claim full abstraction or
unrestricted adequacy for arbitrary recursive programs.
Allocation, reset, and general CP instruments are not quantum functions, so
the qCPO-function category alone cannot instantiate these operations.

## Staging and circuit normal form

- `QLambda.Linear.elaborates_deterministic`
- `QLambda.Linear.elaborates_type_preservation`
- `QLambda.Linear.elaborates_resource_preservation`
- `QLambda.Linear.elaborates_command_wellFormed`
- `QLambda.Linear.elaborates_allocation_bounds`
- `QLambda.Linear.elaborates_compile_agreement`
- `QLambda.Linear.Command.circuit_complete`
- `QLambda.Linear.Command.wellFormed_circuit_complete`
- `QLambda.Linear.Command.compile_wellFormed`

## Canonical lambda quotation

One-wire compatibility layer:

- `QLambda.Linear.Command.quote_typed`
- `QLambda.Linear.Command.Quotation.compile_reflect`
- `QLambda.Linear.Command.Quotation.denote_compile`
- `QLambda.Linear.Command.Quotation.denote_reflect`
- `QLambda.Linear.Command.Quotation.reflect_compile`

Two-wire supported fragment:

- `QLambda.Linear.Command.GeneralQuotation.quote_typed`
- `QLambda.Linear.Command.GeneralQuotation.Quotation.typing`
- `QLambda.Linear.Command.GeneralQuotation.Quotation.compile_reflect`
- `QLambda.Linear.Command.GeneralQuotation.Quotation.denote_compile`
- `QLambda.Linear.Command.GeneralQuotation.Quotation.denote_reflect`
- `QLambda.Linear.Command.GeneralQuotation.Quotation.quotation_capstone`

The supported fragment includes single-wire gates, distinct-wire CX, reset,
measurement, store, sequencing, conditionals, and bounded repeat. Unsupported
coin commands are excluded by `coin_not_quotable`.

## OpenQASM interchange

- `QLambda.Composer.parseStructuredProgram_render_roundTrip`
- `QLambda.Composer.Program.parse_render_roundTrip`
- `QLambda.Composer.parseStructuredProgram_toOpenQASM_roundTrip`
- `QLambda.Composer.Fixtures.bell_openQASM_parse_succeeds`
- `QLambda.Composer.Fixtures.dynamicX_openQASM_parse_succeeds`

The parser theorem covers the declared canonical structured subset, not
arbitrary OpenQASM 3 text.

## Palomar capstones

`Solution.lean` proves:

- `QLambda.Palomar.quantum_lnl_model`
- `QLambda.Palomar.quantum_cpo_enriched_category`
- `QLambda.Palomar.two_wire_circuit_completeness`

`Challenge.lean` contains the matching statement holes by convention.
