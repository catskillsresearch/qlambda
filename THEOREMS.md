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

## Minimum CP-presheaf source fragment

- `QLambda.Linear.Ty.SemanticFragment`
- `QLambda.Linear.Term.SemanticFragment`
- `QLambda.Linear.quotationTy_semanticFragment`
- `QLambda.Linear.generalQuotationTy_semanticFragment`
- `QLambda.Linear.routeA_fragment_acceptance`
- `QLambda.Linear.routeA_succeeded`
- `QLambda.Linear.FragCert.toHasType`
- `QLambda.Linear.fragment_unit_adequacy`
- `QLambda.Linear.fragment_bitLit_adequacy`
- `QLambda.Linear.fragment_step_preserves`
- `QLambda.Linear.fragment_measStep_preserves`
- `QLambda.Linear.fragment_program_complete`

Route A supplies `PresheafFragmentModel` / `routeAFragmentModel` with
classical-bit discard/copy and primitive/measurement Yoneda maps, without a
global bang or `LNLModel`.  Routes B–F are skipped.  Closed unit/bit
adequacy and fragment step/measurement preservation are checked; full
higher-order / recursive adequacy remains an objective.

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
are not all-dimensional cofree promotion. `tensorPowerDimension_mul_add`
only identifies the Hilbert dimension of a fixed-degree partition.
`tensor_finite_subfamily_cp_sum` is joint trace-nonincrease for the tensor of
two families already summable at fixed dimensions.

### Bang comonoid and cofree UP for `A ≤ 1`

- `QLambda.Domain.Presheaf.SuperoperatorModule.bangComultComponentsAdmissible_zero`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangComultComponentsAdmissible_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangComultComponentsAdmissible_of_le_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangComonoid`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangCofreeEquiv_of_le_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangPromote`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangMap`

These close the genuine Day comonoid and cofree universal property
`ComonoidHom(C, !A) ≃ Hom(C, representable A)` for dimensions `A ≤ 1`, with
induced co-Kleisli promotion. They are not an all-dimensional exponential.

### Kernel-checked TNI / Route A obstructions

- `QLambda.Domain.Presheaf.SigmaMon.ChoiSum.exists_fiber2_comp_without_superoperator_sum`
- `QLambda.Domain.Presheaf.SigmaMon.ChoiSum.not_exists_hasSum_gate3Composed`
- `QLambda.Domain.Presheaf.SuperoperatorModule.not_bangSplitFamilyEffectLe_two_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangSplitFamily_effect_le`
- `QLambda.Domain.Presheaf.SuperoperatorModule.routeA_refutation_exists`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangSplitEffectAdmissible_excludes_identity_two`
- `QLambda.Domain.Presheaf.SuperoperatorModule.raw_global_effect_bound_fails_at_two`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangNormalizedSplitFamilyEffect_two_one_eq_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangNormalizedSplitFamilyEffect_two_one_le_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.leftCounit_forces_zero_one_weight_one_of_le_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.rightCounit_forces_one_zero_weight_one_of_le_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.half_scale_not_counital_bang_repair`

Generic joint TNI precomposition at fiber dimension `d ≥ 2`
(`act_sum_from_dim` / `ChoiSum.comp_from_dim`) is false for representable
modules. Separately, the canonical raw bang-split family has joint effect
`(k+1) • effect(coeff)`, so the proposed Route A joint-effect bound fails
already at `A = 2`, degree `1`. `BangSplitEffectAdmissible` is that global
universal bound (not a hereditary carrier-membership predicate); it fails at
`A = 2` by excluding the degree-one identity series. Scaling the degree-one
joint effect by `1/2` repairs the `(2,1)` matrix inequality to `I`, but
left/right counit force the `(0,1)` and `(1,0)` boundary weights to remain
`1`, so uniform half-scaling is not a counital repair. Day admissibility
transfer (`BangComultDayTransferWitness`) remains open. Ambient CP still
admits `CPMapSum.comp_from_dim`. These results do not by themselves prove
`¬ BangComultComponentsAdmissible 2`.

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
measurement, store, sequencing, and conditionals. Unsupported
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
The two fixture parses are checked by `native_decide`, which trusts compiled
evaluation in addition to the kernel.

## Palomar capstones

`Solution.lean` proves:

- `QLambda.Palomar.source_type_safety`: closed-program progress, preservation
  under classical and measurement steps, and determinism of classical steps;
- `QLambda.Palomar.two_wire_quotation_typed`: every supported two-wire
  command quotes to a closed term of the canonical register type.

`Challenge.lean` imports only Mathlib and contains the matching statement
holes by convention. The categorical existence results `quantumLNL` and
`qCPOCategory` are not on the compared surface: `Nonempty` of either bundled
structure is also witnessed by a one-object model with singleton homs.

## Unmet semantic objectives

The following are goals, not existing declarations:

- all-dimensional `BangComultComponentsAdmissible A` for `A ≥ 2`, and a
  premise-free all-dimensional Day bang comonoid / cofree UP (Route A and
  the global raw split-effect bound are refuted; half-scaling repairs the
  `(2,1)` matrix bound but is not counital;
  `BangComultDayTransferWitness` remains open);
- general Day tensor and internal hom for arbitrary based / biorthogonal
  modules beyond the representable fragment.  The coefficientwise
  `symmetricFormalTensorSquare` is not the Day tensor;
- Day factorization of contraction for `A ≥ 2`
  (`SymmetricContractionDayFactorization` is proved only for `A ≤ 1`);
- bang as a functor / comonad on the full linear category (beyond
  representable dimensions `A ≤ 1`), including digging `!A → !!A`;
- the based double-dual classical subcategory and its general Day tensor,
  internal hom, additives, and omega-CPO enrichment;
- a premise-free LNL model `presheafQuantumLNL` whose homs contain
  allocation, reset, gates, and measurement instruments;
- interpretation of all source types and strictly positive recursive types;
- a concrete structural source denotation independent of typing derivations;
- semantic substitution, operational soundness, and fix/fold equations;
- adequacy for closed terms with first-order observable results via
  subnormalized finite approximants;
- preservation of source denotation by successful staging and canonical
  circuit quotation.
