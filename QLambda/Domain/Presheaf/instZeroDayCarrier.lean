/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.DayCoend
import QLambda.Domain.Presheaf.instZeroDayRaw
import QLambda.Domain.Presheaf.setoid

/-!
# Instance `instZeroDayCarrier`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
namespace DayCoend

open Classical

noncomputable instance instZeroDayCarrier (M N : Module.{0}) (n : ℕ) : Zero (Carrier M N n) :=
  ⟨zero M N n⟩

end DayCoend
end SuperoperatorModule
end QLambda.Domain.Presheaf
