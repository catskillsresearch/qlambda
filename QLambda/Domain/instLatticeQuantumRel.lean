/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Domain.QuantumRel
public import QLambda.Domain.instLEQuantumRel
public import QLambda.Domain.instPartialOrderQuantumRel
public import QLambda.Domain.instBotQuantumRel
public import QLambda.Domain.instTopQuantumRel
public import QLambda.Domain.instInfSetQuantumRel
public import QLambda.Domain.instSupSetQuantumRel
public import QLambda.Domain.instSemilatticeInfQuantumRel
public import QLambda.Domain.instSemilatticeSupQuantumRel

@[expose] public section

/-!
# Instance `instLatticeQuantumRel`
-/

namespace QLambda.Domain
namespace QuantumRel

open Matrix
variable {X Y Z W : QuantumSet}

instance instLatticeQuantumRel : Lattice (QuantumRel X Y) where

end QuantumRel
end QLambda.Domain
