/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.DayCoend

/-!
# Instance `instZeroDayRaw`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
namespace DayCoend
namespace Raw

open Classical

instance instZeroDayRaw {M N : Module.{0}} {n : ℕ} : Zero (Raw M N n) :=
  ⟨.zero⟩

end Raw
end DayCoend
end SuperoperatorModule
end QLambda.Domain.Presheaf
