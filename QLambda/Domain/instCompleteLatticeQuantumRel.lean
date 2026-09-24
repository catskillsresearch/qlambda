/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.QuantumRel
import QLambda.Domain.instLEQuantumRel
import QLambda.Domain.instPartialOrderQuantumRel
import QLambda.Domain.instBotQuantumRel
import QLambda.Domain.instTopQuantumRel
import QLambda.Domain.instInfSetQuantumRel
import QLambda.Domain.instSupSetQuantumRel
import QLambda.Domain.instSemilatticeInfQuantumRel
import QLambda.Domain.instSemilatticeSupQuantumRel
import QLambda.Domain.instLatticeQuantumRel
import QLambda.Domain.instBoundedOrderQuantumRel

/-!
# Instance `instCompleteLatticeQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

theorem isLUB_sSup (s : Set (QuantumRel X Y)) :
    IsLUB s (sSup s) := by
  constructor
  · intro R hR x y
    exact le_iSup_of_le ⟨R, hR⟩ le_rfl
  · intro R hR x y
    apply iSup_le
    intro S
    exact (hR S.property) x y

theorem isGLB_sInf (s : Set (QuantumRel X Y)) :
    IsGLB s (sInf s) := by
  constructor
  · intro R hR x y
    exact iInf_le_of_le ⟨R, hR⟩ le_rfl
  · intro R hR x y
    apply le_iInf
    intro S
    exact (hR S.property) x y

noncomputable instance instCompleteLatticeQuantumRel : CompleteLattice (QuantumRel X Y) where
  isLUB_sSup := isLUB_sSup
  isGLB_sInf := isGLB_sInf

end QuantumRel
end QLambda.Domain
