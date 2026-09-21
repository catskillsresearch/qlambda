/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.CQ.Domain
import QLambda.Composer.Syntax

/-!
# Physical interpretation of Composer primitives

The syntax and structural semantics are independent of a particular gate
library. A `Model` supplies ideal finite-register operations for each generic
gate occurrence, local measurement, and reset. Concrete hardware calibration
and noise are intentionally outside this interface.
-/

namespace QLambda.Composer

/-- Ideal primitive model for one fixed-register Composer circuit. -/
structure Model (q c : ℕ) where
  gate : GateApp q → QuantumOperation (CQ.QDim q) (CQ.QDim q)
  measure : Fin q → QuantumInstrument (CQ.QDim q) (CQ.QDim q) 2
  reset : Fin q → QuantumOperation (CQ.QDim q) (CQ.QDim q)

end QLambda.Composer
