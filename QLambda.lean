/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.QuantumInstrument
public import QLambda.QuantumRuntimeState
public import QLambda.CQ.Domain

public import QLambda.Composer.Denotation
public import QLambda.Composer.Fixtures
public import QLambda.Composer.OpenQASM
public import QLambda.Composer.OpenQASMParser
public import QLambda.Composer.WellFormed

public import QLambda.Domain.OmegaCPO
public import QLambda.Domain.Enriched
public import QLambda.Domain.LinearNonlinear
public import QLambda.Domain.RecursiveTypes
public import QLambda.Domain.QuantumSetInstances
public import QLambda.Domain.QuantumRelInstances
public import QLambda.Domain.QuantumRelational
public import QLambda.Domain.QuantumCPOCategory
public import QLambda.Domain.QObj
public import QLambda.Domain.QuantumCategory
public import QLambda.Domain.QuantumMonoidal
public import QLambda.Domain.DiscreteSet
public import QLambda.Domain.QuantumClassical
public import QLambda.Domain.QuantumLNL
public import QLambda.Domain.Presheaf.CPMapInstances
public import QLambda.Domain.Presheaf.SuperoperatorInstances
public import QLambda.Domain.Presheaf.SuperoperatorInstrument
public import QLambda.Domain.Presheaf.SigmaMon
public import QLambda.Domain.Presheaf.SuperoperatorModule
public import QLambda.Domain.Presheaf.Yoneda
public import QLambda.Domain.Presheaf.Generated
public import QLambda.Domain.Presheaf.PseudoRepresentable
public import QLambda.Domain.Presheaf.Classical
public import QLambda.Domain.Presheaf.ClassicalCategory
public import QLambda.Domain.Presheaf.RepresentableBipolar.Surjectivity
public import QLambda.Domain.Presheaf.ClassicalMonoidal
public import QLambda.Domain.Presheaf.Monoidal
public import QLambda.Domain.Presheaf.DayInternalHom
public import QLambda.Domain.Presheaf.DayTensorCoherence
public import QLambda.Domain.Presheaf.OmegaEnrichedInstances
public import QLambda.Domain.Presheaf.SymmetricPower
public import QLambda.Domain.Presheaf.ClosedGenerated
public import QLambda.Domain.Presheaf.Exponential
public import QLambda.Domain.Presheaf.Comonoid
public import QLambda.Domain.Presheaf.ComonoidHom
public import QLambda.Domain.Presheaf.DayComonoidCofree
public import QLambda.Domain.Presheaf.LNL

public import QLambda.Linear.Syntax
public import QLambda.Linear.Context
public import QLambda.Linear.TypeFormationInstances
public import QLambda.Linear.Typing
public import QLambda.Linear.Metatheory
public import QLambda.Linear.Operational
public import QLambda.Linear.Runtime
public import QLambda.Linear.Circuit
public import QLambda.Linear.RegFile
public import QLambda.Linear.Elaboration
public import QLambda.Linear.Quotation
public import QLambda.Linear.QuotationGeneral
public import QLambda.Linear.DenotationInstances
public import QLambda.Linear.PrimitiveSuperoperator
public import QLambda.Linear.TypeInterpretation
public import QLambda.Linear.SemanticFragment
public import QLambda.Linear.FragmentModel
public import QLambda.Linear.FragmentContext
public import QLambda.Linear.FragmentDenotation
public import QLambda.Linear.FragmentIte
public import QLambda.Linear.FragmentAdequacy
public import QLambda.Linear.FragmentCoherence
public import QLambda.Linear.FragmentUnpairBeta
public import QLambda.Linear.FragmentSubstBeta
public import QLambda.Linear.FragmentRuntimeN
public import QLambda.Linear.FragmentSourceCircuitN
public import QLambda.Linear.FragmentQuoteBridgeExt
public import QLambda.Linear.FragmentNDenotation
public import QLambda.Domain.Presheaf.DayBangBoundary
public import QLambda.Domain.Presheaf.AmbientCPGate8TestSuite
public import QLambda.Domain.Presheaf.AmbientCPBang
public import QLambda.Domain.Presheaf.TrackLDeferral

@[expose] public section

/-!
# Typed linear qlambda

The active root exports the reusable matrix/CP/CQ and Composer layers together
with the typed `Domain` and `Linear` redesign.  The former untyped omega-QVA,
choice, `emit`, physical-scratch, and hardware-adequacy tower is intentionally
not reachable from this import.
-/
