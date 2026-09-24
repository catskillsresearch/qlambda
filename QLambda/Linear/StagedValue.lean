/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.RegFile
import QLambda.Linear.Examples

/-!
# Compile-time staging values
-/

namespace QLambda.Linear

/-- Compile-time values.  Closures and primitive partial applications are
eliminated before a successful result crosses the staging boundary. -/
inductive StagedValue (q c : ℕ) where
  | unit
  | bitLit : Bool → StagedValue q c
  | bitRef : Fin c → StagedValue q c
  | qubit : Fin q → StagedValue q c
  | pair : StagedValue q c → StagedValue q c → StagedValue q c
  | closure : Mode → Ty → Ty → Term →
      List (StagedValue q c) → List (StagedValue q c) → StagedValue q c
  | prim : Prim → StagedValue q c
  | cxControl : Fin q → StagedValue q c

namespace StagedValue

def ty {q c : ℕ} : StagedValue q c → Ty
  | .unit => .unit
  | .bitLit _ | .bitRef _ => .bit
  | .qubit _ => .qubit
  | .pair V W => .tensor V.ty W.ty
  | .closure κ A B _ _ _ => .arrow κ A B
  | .prim p => primTy p
  | .cxControl _ => .arrow .lin .qubit (.tensor .qubit .qubit)

/-- Every wire/slot in a first-order result was allocated by the final file. -/
def Respects {q c : ℕ} (ρ : RegFile q c) : StagedValue q c → Prop
  | .unit | .bitLit _ => True
  | .bitRef b => ρ.AllocatedC b
  | .qubit w => ρ.AllocatedQ w
  | .pair V W => V.Respects ρ ∧ W.Respects ρ
  | .closure _ _ _ _ _ _ | .prim _ | .cxControl _ => False

def respectsB {q c : ℕ} (ρ : RegFile q c) : StagedValue q c → Bool
  | .unit | .bitLit _ => true
  | .bitRef b => ρ.allocatedCB b
  | .qubit w => ρ.allocatedQB w
  | .pair V W => V.respectsB ρ && W.respectsB ρ
  | .closure _ _ _ _ _ _ | .prim _ | .cxControl _ => false

def same {q c : ℕ} : StagedValue q c → StagedValue q c → Bool
  | .unit, .unit => true
  | .bitLit a, .bitLit b => decide (a = b)
  | .bitRef a, .bitRef b => decide (a = b)
  | .qubit a, .qubit b => decide (a = b)
  | .pair A B, .pair A' B' => A.same A' && B.same B'
  | _, _ => false

theorem respectsB_sound {q c : ℕ} {ρ : RegFile q c}
    {V : StagedValue q c} (h : V.respectsB ρ = true) :
    V.Respects ρ := by
  cases V with
  | unit => trivial
  | bitLit b => trivial
  | bitRef b => exact RegFile.allocatedCB_sound h
  | qubit w => exact RegFile.allocatedQB_sound h
  | pair V W =>
      simp only [respectsB, Bool.and_eq_true] at h
      exact ⟨respectsB_sound h.1, respectsB_sound h.2⟩
  | closure κ A B M us ls => simp [respectsB] at h
  | prim p => simp [respectsB] at h
  | cxControl w => simp [respectsB] at h

end StagedValue

end QLambda.Linear
