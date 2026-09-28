/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

module

public import QLambda.Linear.FragmentContextObjects
public import QLambda.Linear.FragmentContextDay
public import QLambda.Linear.FragmentContextSplit
public import QLambda.Linear.FragmentContextComonoid

@[expose] public section

/-!
# Open fragment context objects (Route A)

Barrel re-exporting context objects, Day closed maps, splits, and the
classical-bit comonoid.
-/

namespace QLambda.Linear
namespace FragmentContext

set_option maxHeartbeats 8000000

end FragmentContext
end QLambda.Linear
