/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.KrausFamily
import QLambda.QuantumOperation
import QLambda.QuantumInstrument
import QLambda.FiniteInstrumentComp
import QLambda.QuantumQubit

/-!
# Finite quantum operations and instruments

Barrel re-exporting Kraus families, `QuantumOperation`, `QuantumInstrument`,
`FiniteInstrumentComp`, and qubit primitives.

A finite Kraus family denotes a completely positive map by the
operator-sum formula.  Trace non-increase is recorded separately; an
instrument is a finite family whose *total* outcome probability is
trace non-increasing.

`FiniteInstrumentComp` is the Type-level computational monad of a
fixed finite register with classical outcomes in `D`.
-/

namespace QLambda

end QLambda
