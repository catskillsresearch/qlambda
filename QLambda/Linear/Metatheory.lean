/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Substitution
import QLambda.Linear.Typing

/-!
# Structural metatheory

Scoping is a first prerequisite for capture-avoiding substitution and type
preservation.
-/

namespace QLambda.Linear

open Term

theorem typed_scoped {Γ Δ M A} (h : HasType Γ Δ M A) :
    Scoped Δ.length Γ.length M := by
  induction h with
  | varU hlookup _ _ => exact hlookup.lt_length
  | varL hlookup _ => exact hlookup.lt_length
  | lamU _ _ _ ih => simpa [Scoped] using ih
  | lamL _ ih => simpa [Scoped] using ih
  | appL hsplit _ _ ihF ihX =>
      obtain ⟨hFlen, hXlen⟩ := hsplit.lengths
      exact ⟨hFlen.symm ▸ ihF, hXlen.symm ▸ ihX⟩
  | appU _ _ _ ihF ihX => exact ⟨ihF, ihX⟩
  | unit _ => trivial
  | bitLit _ => trivial
  | pair hsplit _ _ ihM ihN =>
      obtain ⟨hMlen, hNlen⟩ := hsplit.lengths
      exact ⟨hMlen.symm ▸ ihM, hNlen.symm ▸ ihN⟩
  | unpair hsplit _ _ ihM ihK =>
      obtain ⟨hMlen, hKlen⟩ := hsplit.lengths
      exact ⟨hMlen.symm ▸ ihM, hKlen.symm ▸ ihK⟩
  | ite hsplit _ _ _ ihB ihT ihE =>
      obtain ⟨hBlen, hBranchLen⟩ := hsplit.lengths
      exact ⟨hBlen.symm ▸ ihB, hBranchLen.symm ▸ ihT,
        hBranchLen.symm ▸ ihE⟩
  | prim _ => trivial
  | measure hsplit _ _ ihQ ihK =>
      obtain ⟨hQlen, hKlen⟩ := hsplit.lengths
      exact ⟨hQlen.symm ▸ ihQ, hKlen.symm ▸ ihK⟩
  | fix _ _ _ ih => exact ih
  | fold _ ih => exact ih
  | unfold _ ih => exact ih

theorem closed_typed_scoped {M A} (h : HasType [] [] M A) :
    Scoped 0 0 M := by
  simpa using typed_scoped h

theorem shiftLin_closed_typed {d M A} (h : HasType [] [] M A) :
    shiftLin d 0 M = M :=
  shiftLin_eq_of_scoped (closed_typed_scoped h)

theorem shiftUnres_closed_typed {d M A} (h : HasType [] [] M A) :
    shiftUnres d 0 M = M :=
  shiftUnres_eq_of_scoped (closed_typed_scoped h)

end QLambda.Linear
