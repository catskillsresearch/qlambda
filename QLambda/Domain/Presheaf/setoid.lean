/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import QLambda.Domain.Presheaf.DayCoend
import QLambda.Domain.Presheaf.instZeroDayRaw

/-!
# Instance `setoid`
-/

namespace QLambda.Domain.Presheaf
namespace SuperoperatorModule
namespace DayCoend
namespace Term

open Classical

instance setoid (M N : Module) (n : ℕ) : Setoid (Term M N n) where
  r := Equivalent
  iseqv := by
    constructor
    · intro t L β
      rfl
    · intro s t h L β
      exact (h L β).symm
    · intro r s t hrs hst L β
      exact (hrs L β).trans (hst L β)

end Term

/-- Carrier of the Day coend at `n`. -/
abbrev Carrier (M N : Module) (n : ℕ) :=
  Quotient (Term.setoid M N n)

noncomputable def evaluate {M N : Module} {n : ℕ}
    (L : Module) (β : Bilinear M N L) :
    Carrier M N n → (L.obj n).Carrier :=
  Quotient.lift (fun t => t.value L β) (fun _ _ h => h L β)

noncomputable def zeroTerm (M N : Module.{0}) (n : ℕ) : Term M N n :=
  ⟨.zero, Raw.admissible_zero, trivial⟩

noncomputable def zero (M N : Module.{0}) (n : ℕ) : Carrier M N n :=
  Quotient.mk _ (zeroTerm M N n)


end DayCoend
end SuperoperatorModule
end QLambda.Domain.Presheaf
