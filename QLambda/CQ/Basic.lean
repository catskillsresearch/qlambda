/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.QuantumInstrument

/-!
# Basic finite classical--quantum types

This dependency-light module contains the register dimension and store
types used by primitive physical semantics.  It intentionally does not
import the legacy instrument-power or ωQVA developments.
-/

namespace QLambda.CQ

/-- Hilbert-space dimension of a register containing `q` qubits. -/
abbrev QDim (q : ℕ) : ℕ := 2 ^ q

/-- A fixed finite classical bit store. -/
abbrev CStore (c : ℕ) := Fin c → Bool

end QLambda.CQ
