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

def liftLin (k : Nat) : Term → Term
  | .var .lin i => .var .lin (if i < k then i else i + 1)
  | .var .unres i => .var .unres i
  | .lam .lin A M => .lam .lin A (liftLin (k + 1) M)
  | .lam .unres A M => .lam .unres A (liftLin k M)
  | .app F X => .app (liftLin k F) (liftLin k X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (liftLin k M) (liftLin k N)
  | .unpair M K => .unpair (liftLin k M) (liftLin k K)
  | .ite B T E => .ite (liftLin k B) (liftLin k T) (liftLin k E)
  | .prim p => .prim p
  | .measure Q K => .measure (liftLin k Q) (liftLin k K)
  | .fix A M => .fix A (liftLin k M)
  | .fold A M => .fold A (liftLin k M)
  | .unfold M => .unfold (liftLin k M)

def liftUnres (k : Nat) : Term → Term
  | .var .unres i => .var .unres (if i < k then i else i + 1)
  | .var .lin i => .var .lin i
  | .lam .unres A M => .lam .unres A (liftUnres (k + 1) M)
  | .lam .lin A M => .lam .lin A (liftUnres k M)
  | .app F X => .app (liftUnres k F) (liftUnres k X)
  | .unit => .unit
  | .bitLit b => .bitLit b
  | .pair M N => .pair (liftUnres k M) (liftUnres k N)
  | .unpair M K => .unpair (liftUnres k M) (liftUnres k K)
  | .ite B T E => .ite (liftUnres k B) (liftUnres k T) (liftUnres k E)
  | .prim p => .prim p
  | .measure Q K => .measure (liftUnres k Q) (liftUnres k K)
  | .fix A M => .fix A (liftUnres k M)
  | .fold A M => .fold A (liftUnres k M)
  | .unfold M => .unfold (liftUnres k M)

/-- Replace linear de Bruijn index `k`. Indices above `k` decrease. -/
def substLin (k : Nat) (v : Term) : Term → Term
  | .var .lin i =>
      if i < k then .var .lin i
      else if i = k then liftLin k v
      else .var .lin (i - 1)
  | .var .unres i => .var .unres i
  | .lam .lin A M => .lam .lin A (substLin (k + 1) v M)
  | .lam .unres A M => .lam .unres A (substLin k v M)
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
      else if i = k then liftUnres k v
      else .var .unres (i - 1)
  | .var .lin i => .var .lin i
  | .lam .unres A M => .lam .unres A (substUnres (k + 1) v M)
  | .lam .lin A M => .lam .lin A (substUnres k v M)
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

theorem liftLin_noLin {k : Nat} {M : Term} (h : noLin M = true) : liftLin k M = M := by
  induction M generalizing k with
  | var κ i =>
      cases κ with
      | lin => simp [noLin] at h
      | unres => rfl
  | lam κ A M ih =>
      cases κ with
      | lin =>
          simp only [noLin] at h
          simp [liftLin, ih h]
      | unres =>
          simp only [noLin] at h
          simp [liftLin, ih h]
  | app F X ihF ihX =>
      simp only [noLin, Bool.and_eq_true] at h
      simp [liftLin, ihF h.1, ihX h.2]
  | unit => rfl
  | bitLit _ => rfl
  | pair M N ihM ihN =>
      simp only [noLin, Bool.and_eq_true] at h
      simp [liftLin, ihM h.1, ihN h.2]
  | unpair M K ihM ihK =>
      simp only [noLin, Bool.and_eq_true] at h
      simp [liftLin, ihM h.1, ihK h.2]
  | ite B T E ihB ihT ihE =>
      simp only [noLin, Bool.and_eq_true] at h
      rcases h with ⟨⟨hB, hT⟩, hE⟩
      simp [liftLin, ihB hB, ihT hT, ihE hE]
  | prim _ => rfl
  | measure Q K ihQ ihK =>
      simp only [noLin, Bool.and_eq_true] at h
      simp [liftLin, ihQ h.1, ihK h.2]
  | fix A M ih =>
      simp only [noLin] at h
      simp [liftLin, ih h]
  | fold A M ih =>
      simp only [noLin] at h
      simp [liftLin, ih h]
  | unfold M ih =>
      simp only [noLin] at h
      simp [liftLin, ih h]

theorem substLin_zero_noLin {v : Term} (h : noLin v = true) :
    substLin 0 v (.var .lin 0) = v := by
  simp [substLin, liftLin_noLin h]

end Term

end QLambda.Linear
