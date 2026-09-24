/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Denotation
import QLambda.Linear.operationalSetoid

/-!
# Instances from `Denotation`
-/

namespace QLambda.Linear

/-- Exact source meaning modulo deterministic classical computation. -/
abbrev OperationalMeaning := Quotient operationalSetoid

def operationalDenote (M : Term) : OperationalMeaning :=
  Quotient.mk' M

theorem step_sound {M N : Term} (h : Step M N) :
    operationalDenote M = operationalDenote N :=
  Quotient.sound (OperationalEq.step h)

theorem betaL_exact {A M V} (hV : Term.Value V) :
    operationalDenote (.app (.lam .lin A M) V) =
      operationalDenote (Term.substLin 0 V M) :=
  step_sound (.betaL hV)

theorem betaU_exact {A M V} (hV : Term.Value V) :
    operationalDenote (.app (.lam .unres A M) V) =
      operationalDenote (Term.substUnres 0 V M) :=
  step_sound (.betaU hV)

theorem unpair_exact {M N K} (hM : Term.Value M) (hN : Term.Value N) :
    operationalDenote (.unpair (.pair M N) K) =
      operationalDenote (.app (.app K M) N) :=
  step_sound (.unpairBeta hM hN)

theorem unfold_fold_exact {A V} (hV : Term.Value V) :
    operationalDenote (.unfold (.fold A V)) = operationalDenote V :=
  step_sound (.unfoldBeta hV)

theorem fix_exact {A V} (hV : Term.Value V) :
    operationalDenote (.fix A V) =
      operationalDenote (.app V (.fix A V)) :=
  step_sound (.fixBeta hV)

theorem operational_quotient_exact {M N : Term} :
    operationalDenote M = operationalDenote N ↔ OperationalEq M N :=
  Quotient.eq_iff_equiv

end QLambda.Linear
