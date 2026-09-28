/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Linear.FragmentCoherenceCore
public import QLambda.Linear.FragmentIdentityBeta
public import QLambda.Linear.FragmentStepCongruence
public import QLambda.Linear.FragmentUnpairBeta
public import QLambda.Linear.FragmentSubstBeta

@[expose] public section

/-!
# Fragment denotational coherence (Route A)

Barrel re-exporting core soundness, closed identity / unpair β, Step
congruence, and non-identity substitution lemmas.
-/

namespace QLambda.Linear

set_option maxHeartbeats 8000000

end QLambda.Linear
