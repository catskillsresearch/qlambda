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
- `QLambda.Linear.routeA_skips_ordered_bang_routes`
- `QLambda.Linear.FragCert.toHasType`
- `QLambda.Linear.FragCert.term_fragment`
- `QLambda.Linear.FragCert.ofHasType_complete`
- `QLambda.Linear.FragCert.FragmentJudgment`
- `QLambda.Linear.FragCert.fragmentJudgment_of_hasType`
- `QLambda.Linear.FragmentContext.routeA_fragment_context_acceptance`
- `QLambda.Linear.FragmentContext.classicalBitComonoid`
- `QLambda.Linear.iteElimFragment`
- `QLambda.Linear.routeAFragmentBranching`
- `QLambda.Linear.FragCert.denote`
- `QLambda.Linear.routeAFragmentDenotationModel`
- `QLambda.Linear.fragment_unit_adequacy`
- `QLambda.Linear.fragment_bitLit_adequacy`
- `QLambda.Linear.fragment_step_preserves`
- `QLambda.Linear.fragment_measStep_preserves`
- `QLambda.Linear.fragment_closed_literal_adequacy`
- `QLambda.Linear.fragment_closed_literal_denote_sound`
- `QLambda.Linear.fragment_step_denote_sound`
- `QLambda.Linear.fragment_step_denote_sound_iteTrue_closed`
- `QLambda.Linear.fragment_step_denote_sound_iteFalse_closed`
- `QLambda.Linear.FragCert.denote_ite_true_closed`
- `QLambda.Linear.FragCert.denote_ite_false_closed`
- `QLambda.Linear.FragmentContext.combinedOSplit_nil`
- `QLambda.Linear.fragment_day_beta`
- `QLambda.Linear.fragment_day_eta`
- `QLambda.Linear.fragment_subst_lin_spine`
- `QLambda.Linear.fragment_subst_unres_bit_spine`
- `QLambda.Linear.FragmentContext.evalFragmentFirstOrder_abstractLinear`
- `QLambda.Linear.fragment_betaL_id_unit`
- `QLambda.Linear.fragment_betaL_id_bit`
- `QLambda.Linear.fragment_betaU_id_bit`
- `QLambda.Linear.fragment_unpair_beta`
- `QLambda.Linear.fragment_betaL_open_move`
- `QLambda.Linear.fragment_betaU_bit_open_move`
- `QLambda.Linear.fragment_substLin_id_denote_unit`
- `QLambda.Linear.fragment_substLin_id_denote_bit`
- `QLambda.Linear.fragment_substUnres_id_denote_bit`
- `QLambda.Linear.fragment_substUnres_const_denote_bit`
- `QLambda.Linear.fragment_substUnres_const_denote_unit`
- `QLambda.Linear.fragment_step_congruence_sound`
- `QLambda.Linear.fragment_step_denote_sound_upgraded`
- `QLambda.Linear.fragment_step_denote_sound_complete`
- `QLambda.Linear.fragment_measStep_denote_sound`
- `QLambda.Linear.measureProbability_eq_instrument_branch_trace`
- `QLambda.Linear.usesAtMost_measure_new0_cont`
- `QLambda.Linear.FragmentMeasuredSimulation`
- `QLambda.Linear.fragmentMeasuredSimulation`
- `QLambda.Linear.fragment_measured_observable_adequacy`
- `QLambda.Linear.fragment_observable_adequacy`
- `QLambda.Linear.fragment_observable_adequacy_literals`
- `QLambda.Linear.fragmentWeightedSimulation`
- `QLambda.Linear.fragment_quote_has_fragCert`
- `QLambda.Linear.quoteSkipSpine`
- `QLambda.Linear.fragCert_skip_quote_denote`
- `QLambda.Linear.quoteGateSpine`
- `QLambda.Linear.fragCert_x_quote_denote`
- `QLambda.Linear.fragCert_h_quote_denote`
- `QLambda.Linear.command_skip_denote_eq_CQ_skip`
- `QLambda.Linear.fragCert_x_quote_denote_independent`
- `QLambda.Linear.fragCert_h_quote_denote_independent`
- `QLambda.Linear.interpretQuoteSpine`
- `QLambda.Linear.interpret_skip_quote`
- `QLambda.Linear.interpret_x_quote`
- `QLambda.Linear.interpret_h_quote`
- `QLambda.Linear.fragCert_spine_interprets_skip_x_h`
- `QLambda.Linear.fragCert_quote_spine_interprets_skip_x_h`
- `QLambda.Linear.fragment_source_quotation_agreement`
- `QLambda.Linear.fragment_source_elaboration_agreement`
- `QLambda.Linear.fragment_source_circuit_commuting_square`
- `QLambda.Linear.fragment_source_quotation_agreement_literals`
- `QLambda.Linear.UsesAtMostQubits`

Route A supplies `PresheafFragmentModel` / `routeAFragmentModel` with
classical-bit discard/copy and primitive/measurement Yoneda maps, without a
global bang or `LNLModel`.  `FragCert` / `FragmentJudgment` are the canonical
fragment judgment (with `ofHasType` completeness and
`fragmentJudgment_of_hasType`).  `FragmentContext` gives open
unrestricted/linear Day-tensor contexts over `classicalBitModule`, with
`classicalBitComonoid` satisfying the four comonoid laws and Day closed
β/η (`dayEval_dayCurry` / `fragment_day_beta` /
`evalFragmentFirstOrder_abstractLinear`).  `FragmentIte` inhabits
`FragmentBranching.iteElim` via controlled bra⊗id selection, supplies
`FragCert.denote` / `routeAFragmentDenotationModel`, and proves closed FO
`ite` Step soundness plus closed linear and unrestricted identity β
(`fragment_betaL_id_unit` / `_bit`, `fragment_betaU_id_bit`), closed
`unpair` β, open-context move forms, and constant unrestricted subst β.
Step congruence packaging, `fragment_step_denote_sound_complete`, and
`FragmentMeasuredSimulation` (measured `new0` with `|0⟩` Born masses) are
checked; Hom-side quote spines (`quoteSkipSpine` / `quoteGateSpine`) equal
hand-built `FragCert` denotations, and `interpretQuoteSpine` turns a
Hom-level spine equation into a `CQ.Sem` agreeing with `Command.denote` for
skip/x/h without inspecting the source command (spine hypothesis discharged
for every closed certificate of those quotations).  A general
`FragCert.denote`↔`CQ.Sem` interpret for arbitrary quoted commands beyond
skip/x/h remains open.

## Day-bang / Track L boundary

- `QLambda.Domain.Presheaf.SuperoperatorModule.day_bang_architecture_boundary`
- `QLambda.Domain.Presheaf.SuperoperatorModule.day_bang_raw_global_bound_fails_at_two`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangComultDayTransferWitness_not_admissible`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangComultDayTransferWitness_requires_nonadditive_target`
- `QLambda.Domain.Presheaf.SuperoperatorModule.AmbientCPDayBangCategory`
- `QLambda.Domain.Presheaf.SuperoperatorModule.ambientCPDayBangCategory`
- `QLambda.Domain.Presheaf.SuperoperatorModule.AmbientCPGate8TestSuite`
- `QLambda.Domain.Presheaf.SuperoperatorModule.ambientCP_gate8_testSuite`
- `QLambda.Domain.Presheaf.SuperoperatorModule.cpm_target_cannot_supply_day_transfer_pair`
- `QLambda.Domain.Presheaf.SuperoperatorModule.day_bang_l8_resolved_by_ambientCP_replacement`
- `QLambda.Domain.Presheaf.SuperoperatorModule.AmbientCPModule`
- `QLambda.Domain.Presheaf.SuperoperatorModule.BangComultAmbientCPAdmissible`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangComultAmbientCP_degree_row_hasSum`
- `QLambda.Domain.Presheaf.SuperoperatorModule.BangDegreeUnitRectangleHasSum`
- `QLambda.Domain.Presheaf.SuperoperatorModule.not_bangDegreeUnitRectangleHasSum_two`
- `QLambda.Domain.Presheaf.SuperoperatorModule.bangComultAmbientCPAdmissible_two_glue_residual`
- `QLambda.Domain.Presheaf.SuperoperatorModule.AmbientCPComonoid`
- `QLambda.Domain.Presheaf.SuperoperatorModule.ambientCPBangComonoid_of_le_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.day_bang_l9_ambientCP_comonoid_le_one`
- `QLambda.Domain.Presheaf.SuperoperatorModule.day_bang_l9_ambientCP_row_glue_deferred`
- `QLambda.Domain.Presheaf.SuperoperatorModule.day_bang_l9_ambientCP_bang_admissible`
- `QLambda.Domain.Presheaf.SuperoperatorModule.day_bang_l9_absolute_bangComult_two_not_claimed`
- `QLambda.Domain.Presheaf.trackL_presheafQuantumLNL_deferred`
- `QLambda.Domain.Presheaf.trackL_recursive_semantics_deferred`
- `QLambda.Domain.Presheaf.trackL_full_adequacy_deferred`
- `QLambda.Domain.Presheaf.trackL_full_abstraction_deferred`
- `QLambda.Linear.routeA_independent_of_day_bang_two`

Raw `BangSplitEffectAdmissible 2` fails; A≤1 bang components succeed.
Any `BangComultDayTransferWitness` refutes `BangComultComponentsAdmissible 2`,
but no TNI/representable witness is constructed.  L8 resolves via the named
replacement `AmbientCPDayBangCategory` (`cpmModule` fibers) and Gate-8 suite
`ambientCP_gate8_testSuite` / terminal
`day_bang_l8_resolved_by_ambientCP_replacement`.  L9 records relative
AmbientCP bang admissibility for `A ≤ 1`, a degree-row gate at 2,
`AmbientCPComonoid` packaging for `A ≤ 1`, and the precise rectangle no-go
`¬ BangDegreeUnitRectangleHasSum 2`
(`day_bang_l9_ambientCP_bang_admissible` /
`day_bang_l9_ambientCP_row_glue_deferred`).  Glued
`BangComultAmbientCPAdmissible 2` remains open.  Absolute A=2 is not
claimed.  Track L packages remain deferred until A=2 glue or a limited
A≤1 LNL; Route A fragment work does not depend on it.

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
transfer is not constructed in TNI modules; L8 publishes the ambient-CP
replacement `AmbientCPDayBangCategory` instead. Ambient CP still admits
`CPMapSum.comp_from_dim` and `Fiber.HasSumAdd`. These results do not by
themselves prove `¬ BangComultComponentsAdmissible 2` in the TNI setting.

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

The following are goals, not existing declarations.  Route A
`FragCert.denote`, Day closed β/η, closed FO `ite`, closed linear and
unrestricted identity β, closed `unpair` β, open-context lam/app move forms,
constant unrestricted subst β, Step congruence and the complete fragment-
admitted Step package, measured `new0` Born adequacy, Hom-side quote spines
with thin skip/x/h CQ bridge, L8 ambient-CP replacement, and L9 relative
AmbientCP admissibility (`A ≤ 1` + degree-row at 2) are already checked (see
the index above); they are not listed here as open.

- all-dimensional TNI `BangComultComponentsAdmissible A` for `A ≥ 2`, and a
  premise-free all-dimensional Day bang comonoid / cofree UP (Route A and
  the global raw split-effect bound are refuted; L8 selects
  `AmbientCPDayBangCategory` /
  `day_bang_l8_resolved_by_ambientCP_replacement`);
- glued `BangComultAmbientCPAdmissible 2` (A=1-style rectangle glue blocked
  by `¬ BangDegreeUnitRectangleHasSum 2`; `AmbientCPComonoid` for `A ≤ 1`
  is packaged), then premise-free `presheafQuantumLNL`, recursive `mu`/`fix`,
  full-language adequacy, and full abstraction (Track L deferred theorems
  record this boundary; absolute A=2 is not claimed);
- general Day tensor and internal hom for arbitrary based / biorthogonal
  modules beyond the representable fragment.  The coefficientwise
  `symmetricFormalTensorSquare` is not the Day tensor;
- Day factorization of contraction for `A ≥ 2`
  (`SymmetricContractionDayFactorization` is proved only for `A ≤ 1`);
- bang as a functor / comonad on the full linear category (beyond
  representable dimensions `A ≤ 1`), including digging `!A → !!A`;
- the based double-dual classical subcategory and its general Day tensor,
  internal hom, additives, and omega-CPO enrichment;
- interpretation of all source types and strictly positive recursive types;
- a concrete structural source denotation independent of typing derivations
  for the full language (including `fix`/`mu`);
- full abstraction for a named fragment, or a precise no-go boundary.
