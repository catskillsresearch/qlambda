/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.ScottFunction
public import QLambda.Domain.instCoeScottFunction
public import QLambda.Domain.instLEScottFunction

@[expose] public section

/-!
# Instance `instPartialOrderScottFunction`
-/

namespace QLambda.Domain
namespace ScottFunction

instance instPartialOrderScottFunction {P Q : QuantumCPO} : PartialOrder (ScottFunction P Q) where
  le_refl F := by
    change F.toQuantumFunction ≤ F.toQuantumFunction
    exact le_rfl
  le_trans F G H hFG hGH := by
    change F.toQuantumFunction ≤ H.toQuantumFunction
    change F.toQuantumFunction ≤ G.toQuantumFunction at hFG
    change G.toQuantumFunction ≤ H.toQuantumFunction at hGH
    exact hFG.trans hGH
  le_antisymm F G hFG hGF :=
    ext (le_antisymm hFG hGF)

end ScottFunction
end QLambda.Domain
