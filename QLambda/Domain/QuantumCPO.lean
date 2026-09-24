/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRelational

/-!
# Quantum CPOs
-/

namespace QLambda.Domain

/-- A quantum CPO: a quantum poset satisfying the atomic-probe completeness
condition. -/
structure QuantumCPO where
  poset : QuantumPoset
  complete : IsQuantumCPO poset

namespace QuantumCPO

def discrete (X : QuantumSet) [DecidableEq X.Atom] : QuantumCPO where
  poset := .discrete X
  complete := discrete_isQuantumCPO X

def qubit : QuantumCPO := ⟨.qubit, qubit_isQuantumCPO⟩
def bit : QuantumCPO := ⟨.bit, bit_isQuantumCPO⟩
def unit : QuantumCPO := ⟨.unit, unit_isQuantumCPO⟩

end QuantumCPO

end QLambda.Domain
