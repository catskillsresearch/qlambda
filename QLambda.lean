/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.QuantumInstrument
import QLambda.QuantumRuntimeState
import QLambda.CQ.Domain

import QLambda.Composer.Denotation
import QLambda.Composer.Fixtures
import QLambda.Composer.OpenQASM
import QLambda.Composer.OpenQASMParser
import QLambda.Composer.WellFormed

import QLambda.Domain.OmegaCPO
import QLambda.Domain.Enriched
import QLambda.Domain.LinearNonlinear
import QLambda.Domain.RecursiveTypes
import QLambda.Domain.QuantumSet
import QLambda.Domain.QuantumRel
import QLambda.Domain.QuantumRelational
import QLambda.Domain.QuantumCPOCategory
import QLambda.Domain.QuantumCategory
import QLambda.Domain.QuantumMonoidal
import QLambda.Domain.DiscreteSet
import QLambda.Domain.QuantumClassical
import QLambda.Domain.QuantumLNL
import QLambda.Domain.Presheaf.CPMap
import QLambda.Domain.Presheaf.Superoperator
import QLambda.Domain.Presheaf.SigmaMon
import QLambda.Domain.Presheaf.Module
import QLambda.Domain.Presheaf.Yoneda
import QLambda.Domain.Presheaf.Generated
import QLambda.Domain.Presheaf.PseudoRepresentable
import QLambda.Domain.Presheaf.Classical
import QLambda.Domain.Presheaf.ClassicalCategory
import QLambda.Domain.Presheaf.Monoidal
import QLambda.Domain.Presheaf.DayCoend
import QLambda.Domain.Presheaf.OmegaEnriched
import QLambda.Domain.Presheaf.SymmetricPower
import QLambda.Domain.Presheaf.ClosedGenerated
import QLambda.Domain.Presheaf.Exponential

import QLambda.Linear.Syntax
import QLambda.Linear.Context
import QLambda.Linear.TypeFormation
import QLambda.Linear.Typing
import QLambda.Linear.Metatheory
import QLambda.Linear.Operational
import QLambda.Linear.Runtime
import QLambda.Linear.Circuit
import QLambda.Linear.RegFile
import QLambda.Linear.Elaboration
import QLambda.Linear.Quotation
import QLambda.Linear.QuotationGeneral
import QLambda.Linear.Denotation
import QLambda.Linear.PrimitiveSuperoperator
import QLambda.Linear.TypeInterpretation

/-!
# Typed linear qlambda

The active root exports the reusable matrix/CP/CQ and Composer layers together
with the typed `Domain` and `Linear` redesign.  The former untyped omega-QVA,
choice, `emit`, physical-scratch, and hardware-adequacy tower is intentionally
not reachable from this import.
-/
