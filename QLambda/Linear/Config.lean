/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.RuntimeCore

/-!
# Finite-register runtime configurations
-/

namespace QLambda.Linear.Runtime

/-- A fixed finite quantum register and a quantum-kernel control state.
`frame` records live wires owned by the surrounding source evaluation
context; control-owned wires are tracked structurally. -/
structure Config (q : Nat) where
  state : RegisterState q
  frame : Finset (Fin q)
  control : Control q

namespace Config

variable {q : Nat}

def live (s : Config q) : Finset (Fin q) :=
  s.frame ∪ s.control.wires

/-- Static configuration typing: the control has the requested source type,
contains no aliased wire, and is disjoint from wires owned by its frame. -/
def WellTyped (s : Config q) (A : Ty) : Prop :=
  s.control.typeOf = some A ∧
    s.control.Valid ∧
    Disjoint s.control.wires s.frame

/-- A final runtime configuration contains a returned value. -/
def Normal (s : Config q) : Prop :=
  ∃ value, s.control = .ret value

/-- Allocation is the only capacity-sensitive request. -/
def OutOfWires (s : Config q) : Prop :=
  s.control = .app (.prim .new0) .unit ∧ ∀ w : Fin q, w ∈ s.live

end Config

end QLambda.Linear.Runtime
