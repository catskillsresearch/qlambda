/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Linear.FragmentPhysicalBit

/-!
# Instance `instZeroClassicalBitCarrier`
-/

set_option maxHeartbeats 8000000
namespace QLambda.Linear

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable instance instZeroClassicalBitCarrier (n : ℕ) : Zero (ClassicalBitCarrier n) :=
  ⟨⟨0, by simp [Superoperator.comp_zero_right]⟩⟩


end QLambda.Linear
