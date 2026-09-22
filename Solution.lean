/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda

/-! # Sorry-free solutions to the typed-linear Palomar challenge. -/

namespace QLambda.Palomar

open QLambda.Linear

theorem source_type_safety {M : Term} {A : Ty} (h : HasType [] [] M A) :
    MakesProgress M ∧
      (∀ N, Step M N → HasType [] [] N A) ∧
      (∀ b N, MeasStep M b N → HasType [] [] N A) ∧
      (∀ N₁ N₂, Step M N₁ → Step M N₂ → N₁ = N₂) :=
  ⟨progress h,
    fun _ hs => step_preservation hs h,
    fun _ _ hm => measStep_preservation hm h,
    fun _ _ h₁ h₂ => step_deterministic h₁ h₂⟩

theorem two_wire_quotation_typed
    (C : Command
      Command.GeneralQuotation.quantumSize
      Command.GeneralQuotation.classicalSize)
    (hC : Command.GeneralQuotation.Quotable C) :
    HasType [] [] (Command.GeneralQuotation.quote C)
      Command.GeneralQuotation.quotationTy :=
  Command.GeneralQuotation.quote_typed hC

end QLambda.Palomar
