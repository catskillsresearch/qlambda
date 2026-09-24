/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.LinearNonlinear
import QLambda.Domain.QuantumRelational

/-!
# Decidable quantum sets as linear objects
-/

namespace QLambda.Domain

/-- A quantum set with decidable atoms, packaged as a linear object. -/
structure QObj where
  set : QuantumSet
  [decidable : DecidableEq set.Atom]

attribute [instance] QObj.decidable

namespace QObj

def qubit : QObj := ⟨.qubit⟩
def bit : QObj := ⟨.bit⟩
def unit : QObj := ⟨.unit⟩

def tensor (X Y : QObj) : QObj where
  set := X.set.tensor Y.set
  decidable := inferInstanceAs (DecidableEq (X.set.Atom × Y.set.Atom))

def dual (X : QObj) : QObj where
  set := X.set.dual
  decidable := inferInstanceAs (DecidableEq X.set.Atom)

def ofPoset (P : QuantumPoset) : QObj where
  set := P.carrier

end QObj

end QLambda.Domain
