# Typed linear qlambda theorem index

This index lists only declarations that exist in the active replacement
theorem surface.  Unmet semantic objectives are listed separately at the end.

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
- `QLambda.Linear.Runtime.RegisterState.measureProbability_false_add_true`

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
- `QLambda.Linear.qubitMeasurement`

`CompletedCP` identifies Kraus presentations by intrinsic semantic
refinement. It is a first-order presentation, not the higher-order category.

## CP-enriched presheaf foundation

These declarations construct the finite CP/TNI substrate and the specialized
module fragment used by the remaining semantic objective. They are not an
LNL instance, a source denotation, or an adequacy theorem.

- `QLambda.Domain.Presheaf.CPMap.completedEquiv`
- `QLambda.Domain.Presheaf.CPMap.toCompleted_ofKraus`
- `QLambda.Domain.Presheaf.CPMap.ofCompleted_toCompleted`
- `QLambda.Domain.Presheaf.CPMap.toCompleted_ofCompleted`
- `QLambda.Domain.Presheaf.CPMap.le_iff_exists_add`
- `QLambda.Domain.Presheaf.CPMap.effectNorm_nnsmul`
- `QLambda.Domain.Presheaf.Superoperator.ofQuantumOperation_toQuantumOperation`
- `QLambda.Domain.Presheaf.Superoperator.ofLE`
- `QLambda.Domain.Presheaf.Superoperator.comp_assoc`
- `QLambda.Domain.Presheaf.Superoperator.tensor_comp`
- `QLambda.Domain.Presheaf.Superoperator.cp_allocateZero`
- `QLambda.Domain.Presheaf.Superoperator.cp_reset`
- `QLambda.Domain.Presheaf.Instrument.measure_branch_zero`
- `QLambda.Domain.Presheaf.Instrument.measure_branch_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.yonedaMap_id`
- `QLambda.Domain.Presheaf.SuperoperatorModule.yonedaMap_comp`
- `QLambda.Domain.Presheaf.SuperoperatorModule.yonedaEquiv`
- `QLambda.Domain.Presheaf.SigmaMon.cpMapPartialCountableSum`
- `QLambda.Domain.Presheaf.SuperoperatorModule.cpmModule`
- `QLambda.Domain.Presheaf.SuperoperatorModule.PseudoRepresentable.toAmbient`
- `QLambda.Domain.Presheaf.SuperoperatorModule.PseudoBasis.matrixOfHom`
- `QLambda.Domain.Presheaf.SuperoperatorModule.PseudoBasis.AdmissibleMatrix.comp`
- `QLambda.Domain.Presheaf.SuperoperatorModule.dayTensorRepresentablePresentation`
- `QLambda.Domain.Presheaf.SuperoperatorModule.curry_uncurry_representable`
- `QLambda.Domain.Presheaf.SuperoperatorModule.uncurry_curry_representable`
- `QLambda.Domain.Presheaf.SuperoperatorModule.closedTensorRepresentable_module`
- `QLambda.Domain.Presheaf.SuperoperatorModule.symmetricAverage_idempotent`
- `QLambda.Domain.Presheaf.SuperoperatorModule.symmetricContraction_cocommutative`
- `QLambda.Domain.Presheaf.SuperoperatorModule.symmetricContraction_coassociative`
- `QLambda.Domain.Presheaf.SuperoperatorModule.tensorPowerDimension_mul_add`
- `QLambda.Domain.Presheaf.SigmaMon.ChoiSum.tensor_finite_subfamily_cp_sum`

`symmetricContraction` and `symmetricEquivalencePromotion` are a
symmetric-series comonoid and an action of finite basis equivalences. They
are not cofree promotion. The cofree universal property would be
`ComonoidHom(C, !A) ≃ Hom(C, A)`, inducing
`Hom(!B, A) → Hom(!B, !A)`. `tensorPowerDimension_mul_add` only identifies the
Hilbert dimension of a fixed-degree partition.
`tensor_finite_subfamily_cp_sum` is joint trace-nonincrease for the tensor of
two families already summable at fixed dimensions.
- `QLambda.Linear.Prim.superoperator_completedCP`
- `QLambda.Linear.qubitInstrument_zero`
- `QLambda.Linear.qubitInstrument_one`
- `QLambda.Linear.Ty.FirstOrder.object_tensor`

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
source equations by construction; it is not an instantiated denotational
model or an adequacy theorem. The repository does not claim full abstraction
or unrestricted adequacy for arbitrary recursive programs.
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

`Quotation.denote` and `GeneralQuotation.Quotation.denote` are defined from
the represented command.  Their `denote_compile` results are exact CQ
equalities, not source-denotation preservation theorems.

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

## Unmet semantic objectives

The following are goals, not existing declarations:

- mixed-partition trace-nonincrease: a joint bound on homogeneous branches
  does not yet transport to a sum of tensors whose factors lie in different
  symmetric-power degrees;
- general Day tensor and internal hom for based modules.  The current
  coefficientwise `symmetricFormalTensorSquare` is not proved to be the Day
  tensor of two symmetric-series modules;
- factorization of coordinatewise contraction through that genuine Day
  tensor.  The identity-in-every-degree series is required by cofreeness and
  is not a counterexample: different degree splits are tensor coordinates,
  not branches to be added;
- the cofree universal property `ComonoidHom(C, !A) ≃ Hom(C, A)`, its induced
  co-Kleisli promotion `Hom(!B, A) → Hom(!B, !A)`, and the resulting comonad;
- the based double-dual classical subcategory and its general Day tensor,
  internal hom, additives, and omega-CPO enrichment;
- a premise-free LNL model whose homs contain allocation, reset, gates, and
  measurement instruments;
- interpretation of all source types and strictly positive recursive types;
- a concrete structural source denotation independent of typing derivations;
- semantic substitution, operational soundness, and fix/fold equations;
- adequacy for closed terms with first-order observable results via
  subnormalized finite approximants;
- preservation of source denotation by successful staging and canonical
  circuit quotation.
