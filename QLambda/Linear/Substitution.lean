/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.Syntax

/-!
# De Bruijn substitution

Linear and unrestricted substitution are separate. A replacement is lifted
when it passes under a binder of the same mode.
-/

namespace QLambda.Linear

namespace Term

/-- Both de Bruijn namespaces are locally scoped. -/
def Scoped (linearDepth unresDepth : Nat) : Term → Prop
  | .var .lin i => i < linearDepth
  | .var .unres i => i < unresDepth
  | .lam .lin _ M => Scoped (linearDepth + 1) unresDepth M
  | .lam .unres _ M => Scoped linearDepth (unresDepth + 1) M
  | .app F X => Scoped linearDepth unresDepth F ∧ Scoped linearDepth unresDepth X
  | .unit => True
  | .bitLit _ => True
  | .pair M N => Scoped linearDepth unresDepth M ∧ Scoped linearDepth unresDepth N
  | .unpair M K => Scoped linearDepth unresDepth M ∧ Scoped linearDepth unresDepth K
  | .ite B T E =>
      Scoped linearDepth unresDepth B ∧
      Scoped linearDepth unresDepth T ∧ Scoped linearDepth unresDepth E
  | .prim _ => True
  | .measure Q K => Scoped linearDepth unresDepth Q ∧ Scoped linearDepth unresDepth K
  | .fix _ M => Scoped linearDepth unresDepth M
  | .fold _ M => Scoped linearDepth unresDepth M
  | .unfold M => Scoped linearDepth unresDepth M

def shiftLin (d cutoff : Nat) : Term → Term
  | .var .lin i => .var .lin (if i < cutoff then i else i + d)
  | .var .unres i => .var .unres i
  | .lam .lin A M => .lam .lin A (shiftLin d (cutoff + 1) M)
  | .lam .unres A M => .lam .unres A (shiftLin d cutoff M)
  | .app F X => .app (shiftLin d cutoff F) (shiftLin d cutoff X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (shiftLin d cutoff M) (shiftLin d cutoff N)
  | .unpair M K => .unpair (shiftLin d cutoff M) (shiftLin d cutoff K)
  | .ite B T E =>
      .ite (shiftLin d cutoff B) (shiftLin d cutoff T) (shiftLin d cutoff E)
  | .prim p => .prim p
  | .measure Q K => .measure (shiftLin d cutoff Q) (shiftLin d cutoff K)
  | .fix A M => .fix A (shiftLin d cutoff M)
  | .fold A M => .fold A (shiftLin d cutoff M)
  | .unfold M => .unfold (shiftLin d cutoff M)

def shiftUnres (d cutoff : Nat) : Term → Term
  | .var .unres i => .var .unres (if i < cutoff then i else i + d)
  | .var .lin i => .var .lin i
  | .lam .unres A M => .lam .unres A (shiftUnres d (cutoff + 1) M)
  | .lam .lin A M => .lam .lin A (shiftUnres d cutoff M)
  | .app F X => .app (shiftUnres d cutoff F) (shiftUnres d cutoff X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (shiftUnres d cutoff M) (shiftUnres d cutoff N)
  | .unpair M K => .unpair (shiftUnres d cutoff M) (shiftUnres d cutoff K)
  | .ite B T E =>
      .ite (shiftUnres d cutoff B) (shiftUnres d cutoff T) (shiftUnres d cutoff E)
  | .prim p => .prim p
  | .measure Q K => .measure (shiftUnres d cutoff Q) (shiftUnres d cutoff K)
  | .fix A M => .fix A (shiftUnres d cutoff M)
  | .fold A M => .fold A (shiftUnres d cutoff M)
  | .unfold M => .unfold (shiftUnres d cutoff M)

abbrev liftLin := shiftLin 1
abbrev liftUnres := shiftUnres 1

theorem shiftLin_eq_of_scoped {d l u : Nat} {M : Term}
    (h : Scoped l u M) : shiftLin d l M = M := by
  induction M generalizing l u with
  | var κ i =>
      cases κ with
      | lin =>
          change i < l at h
          simp [shiftLin, h]
      | unres => rfl
  | lam κ A M ih =>
      cases κ with
      | lin => simp [Scoped] at h; simp [shiftLin, ih h]
      | unres => simp [Scoped] at h; simp [shiftLin, ih h]
  | app F X ihF ihX =>
      rcases h with ⟨hF, hX⟩
      simp [shiftLin, ihF hF, ihX hX]
  | unit => rfl
  | bitLit _ => rfl
  | pair M N ihM ihN =>
      rcases h with ⟨hM, hN⟩
      simp [shiftLin, ihM hM, ihN hN]
  | unpair M K ihM ihK =>
      rcases h with ⟨hM, hK⟩
      simp [shiftLin, ihM hM, ihK hK]
  | ite B T E ihB ihT ihE =>
      rcases h with ⟨hB, hT, hE⟩
      simp [shiftLin, ihB hB, ihT hT, ihE hE]
  | prim _ => rfl
  | measure Q K ihQ ihK =>
      rcases h with ⟨hQ, hK⟩
      simp [shiftLin, ihQ hQ, ihK hK]
  | fix A M ih => simp [Scoped] at h; simp [shiftLin, ih h]
  | fold A M ih => simp [Scoped] at h; simp [shiftLin, ih h]
  | unfold M ih => simp [Scoped] at h; simp [shiftLin, ih h]

theorem shiftUnres_eq_of_scoped {d l u : Nat} {M : Term}
    (h : Scoped l u M) : shiftUnres d u M = M := by
  induction M generalizing l u with
  | var κ i =>
      cases κ with
      | lin => rfl
      | unres =>
          change i < u at h
          simp [shiftUnres, h]
  | lam κ A M ih =>
      cases κ with
      | lin => simp [Scoped] at h; simp [shiftUnres, ih h]
      | unres => simp [Scoped] at h; simp [shiftUnres, ih h]
  | app F X ihF ihX =>
      rcases h with ⟨hF, hX⟩
      simp [shiftUnres, ihF hF, ihX hX]
  | unit => rfl
  | bitLit _ => rfl
  | pair M N ihM ihN =>
      rcases h with ⟨hM, hN⟩
      simp [shiftUnres, ihM hM, ihN hN]
  | unpair M K ihM ihK =>
      rcases h with ⟨hM, hK⟩
      simp [shiftUnres, ihM hM, ihK hK]
  | ite B T E ihB ihT ihE =>
      rcases h with ⟨hB, hT, hE⟩
      simp [shiftUnres, ihB hB, ihT hT, ihE hE]
  | prim _ => rfl
  | measure Q K ihQ ihK =>
      rcases h with ⟨hQ, hK⟩
      simp [shiftUnres, ihQ hQ, ihK hK]
  | fix A M ih => simp [Scoped] at h; simp [shiftUnres, ih h]
  | fold A M ih => simp [Scoped] at h; simp [shiftUnres, ih h]
  | unfold M ih => simp [Scoped] at h; simp [shiftUnres, ih h]

/-- Replace linear de Bruijn index `k`. Indices above `k` decrease. -/
def substLin (k : Nat) (v : Term) : Term → Term
  | .var .lin i =>
      if i < k then .var .lin i
      else if i = k then shiftLin k 0 v
      else .var .lin (i - 1)
  | .var .unres i => .var .unres i
  | .lam .lin A M => .lam .lin A (substLin (k + 1) v M)
  | .lam .unres A M =>
      .lam .unres A (substLin k (shiftUnres 1 0 v) M)
  | .app F X => .app (substLin k v F) (substLin k v X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (substLin k v M) (substLin k v N)
  | .unpair M K => .unpair (substLin k v M) (substLin k v K)
  | .ite B T E => .ite (substLin k v B) (substLin k v T) (substLin k v E)
  | .prim p => .prim p
  | .measure Q K => .measure (substLin k v Q) (substLin k v K)
  | .fix A M => .fix A (substLin k v M)
  | .fold A M => .fold A (substLin k v M)
  | .unfold M => .unfold (substLin k v M)

/-- Replace unrestricted de Bruijn index `k`. -/
def substUnres (k : Nat) (v : Term) : Term → Term
  | .var .unres i =>
      if i < k then .var .unres i
      else if i = k then shiftUnres k 0 v
      else .var .unres (i - 1)
  | .var .lin i => .var .lin i
  | .lam .unres A M => .lam .unres A (substUnres (k + 1) v M)
  | .lam .lin A M =>
      .lam .lin A (substUnres k (shiftLin 1 0 v) M)
  | .app F X => .app (substUnres k v F) (substUnres k v X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (substUnres k v M) (substUnres k v N)
  | .unpair M K => .unpair (substUnres k v M) (substUnres k v K)
  | .ite B T E => .ite (substUnres k v B) (substUnres k v T) (substUnres k v E)
  | .prim p => .prim p
  | .measure Q K => .measure (substUnres k v Q) (substUnres k v K)
  | .fix A M => .fix A (substUnres k v M)
  | .fold A M => .fold A (substUnres k v M)
  | .unfold M => .unfold (substUnres k v M)

/-- True when `M` contains no linear variable. -/
def noLin : Term → Bool
  | .var .lin _ => false
  | .var .unres _ => true
  | .lam _ _ M => noLin M
  | .app F X => noLin F && noLin X
  | .unit => true
  | .bitLit _ => true
  | .pair M N => noLin M && noLin N
  | .unpair M K => noLin M && noLin K
  | .ite B T E => noLin B && noLin T && noLin E
  | .prim _ => true
  | .measure Q K => noLin Q && noLin K
  | .fix _ M => noLin M
  | .fold _ M => noLin M
  | .unfold M => noLin M

theorem shiftLin_noLin {d cutoff : Nat} {M : Term} (h : noLin M = true) :
    shiftLin d cutoff M = M := by
  induction M generalizing cutoff with
  | var κ i =>
      cases κ with
      | lin => simp [noLin] at h
      | unres => rfl
  | lam κ A M ih =>
      cases κ with
      | lin =>
          simp only [noLin] at h
          simp [shiftLin, ih h]
      | unres =>
          simp only [noLin] at h
          simp [shiftLin, ih h]
  | app F X ihF ihX =>
      simp only [noLin, Bool.and_eq_true] at h
      simp [shiftLin, ihF h.1, ihX h.2]
  | unit => rfl
  | bitLit _ => rfl
  | pair M N ihM ihN =>
      simp only [noLin, Bool.and_eq_true] at h
      simp [shiftLin, ihM h.1, ihN h.2]
  | unpair M K ihM ihK =>
      simp only [noLin, Bool.and_eq_true] at h
      simp [shiftLin, ihM h.1, ihK h.2]
  | ite B T E ihB ihT ihE =>
      simp only [noLin, Bool.and_eq_true] at h
      rcases h with ⟨⟨hB, hT⟩, hE⟩
      simp [shiftLin, ihB hB, ihT hT, ihE hE]
  | prim _ => rfl
  | measure Q K ihQ ihK =>
      simp only [noLin, Bool.and_eq_true] at h
      simp [shiftLin, ihQ h.1, ihK h.2]
  | fix A M ih =>
      simp only [noLin] at h
      simp [shiftLin, ih h]
  | fold A M ih =>
      simp only [noLin] at h
      simp [shiftLin, ih h]
  | unfold M ih =>
      simp only [noLin] at h
      simp [shiftLin, ih h]

theorem shiftLin_zero (cutoff : Nat) (M : Term) : shiftLin 0 cutoff M = M := by
  induction M generalizing cutoff with
  | var κ i =>
      cases κ <;> simp [shiftLin]
  | lam κ A M ih =>
      cases κ <;> simp [shiftLin, ih]
  | app F X ihF ihX => simp [shiftLin, ihF, ihX]
  | unit => rfl
  | bitLit _ => rfl
  | pair M N ihM ihN => simp [shiftLin, ihM, ihN]
  | unpair M K ihM ihK => simp [shiftLin, ihM, ihK]
  | ite B T E ihB ihT ihE => simp [shiftLin, ihB, ihT, ihE]
  | prim _ => rfl
  | measure Q K ihQ ihK => simp [shiftLin, ihQ, ihK]
  | fix A M ih => simp [shiftLin, ih]
  | fold A M ih => simp [shiftLin, ih]
  | unfold M ih => simp [shiftLin, ih]

theorem liftLin_noLin {k : Nat} {M : Term} (h : noLin M = true) :
    liftLin k M = M :=
  shiftLin_noLin h

theorem substLin_zero_noLin {v : Term} (_h : noLin v = true) :
    substLin 0 v (.var .lin 0) = v := by
  simp [substLin, shiftLin_zero]

theorem substLin_avoids_unrestricted_capture :
    substLin 0 (.var .unres 0)
        (.lam .unres .bit (.var .lin 0)) =
      .lam .unres .bit (.var .unres 1) := by
  rfl

theorem substUnres_avoids_linear_capture :
    substUnres 0 (.var .lin 0)
        (.lam .lin .qubit (.var .unres 0)) =
      .lam .lin .qubit (.var .lin 1) := by
  rfl

end Term

end QLambda.Linear
