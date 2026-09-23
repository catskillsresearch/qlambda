/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentDenotation
import QLambda.Linear.FragmentAdequacy
import QLambda.Linear.Operational

/-!
# Fragment denotational coherence (Route A)

Closed literal denotations are stable under the operational equations that
apply to values (no `Step` from unit/bit literals).  Full open-term β/η and
substitution lemmas remain Track F objectives layered on `FragmentContext`.
-/

namespace QLambda.Linear

/-- Unit and bit literals are values, so no closed `Step` applies. -/
theorem fragment_closed_literal_not_step {M M' : Term}
    (h : M = .unit ∨ ∃ b, M = .bitLit b) (hs : Step M M') : False := by
  rcases h with rfl | ⟨b, rfl⟩
  · cases hs
  · cases hs

/-- Denotational soundness for closed unit: denotation equals Route A intro. -/
theorem fragment_step_denote_sound_unit
    (c : FragCert.Closed .unit .unit) :
    FragCert.denoteUnit c = routeAFragmentModel.unitIntro :=
  FragCert.denoteUnit_eq c

/-- Denotational soundness for closed bit literals. -/
theorem fragment_step_denote_sound_bitLit {b : Bool}
    (c : FragCert.Closed (.bitLit b) .bit) :
    FragCert.denoteBitLit c = routeAFragmentModel.bitLit b :=
  FragCert.denoteBitLit_eq c

/-- Combined closed-literal denotational soundness package. -/
theorem fragment_closed_literal_denote_sound :
    (∀ c : FragCert.Closed .unit .unit,
      FragCert.denoteUnit c = routeAFragmentModel.unitIntro) ∧
    (∀ b (c : FragCert.Closed (.bitLit b) .bit),
      FragCert.denoteBitLit c = routeAFragmentModel.bitLit b) :=
  ⟨fragment_step_denote_sound_unit, fun _ => fragment_step_denote_sound_bitLit⟩

end QLambda.Linear
