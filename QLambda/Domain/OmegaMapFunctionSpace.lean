/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.OmegaMap

/-!
# Function space of ω-continuous maps
-/

namespace QLambda.Domain

universe u v

namespace OmegaMap

section FunctionSpace

variable {D : Type u} {E : Type v}
  [PartialOrder D] [OmegaComplete D]
  [PartialOrder E] [OmegaComplete E]

/-- Continuous maps form an ωCPO under the pointwise order. -/
noncomputable instance instOmegaCompleteFunctionSpace :
    OmegaComplete (OmegaMap D E) where
  ωSup c hc :=
    { toFun := fun x =>
        OmegaComplete.ωSup (fun n => c n x)
          (fun _ _ h => hc h x)
      monotone := by
        intro x y hxy
        exact OmegaComplete.ωSup_mono _ _
          (fun n => (c n).monotone hxy)
      map_ωSup := by
        intro x hx
        apply le_antisymm
        · apply OmegaComplete.ωSup_le
          intro n
          rw [(c n).map_ωSup x hx]
          apply OmegaComplete.ωSup_le
          intro m
          let k := max n m
          have hnk : n ≤ k := Nat.le_max_left _ _
          have hmk : m ≤ k := Nat.le_max_right _ _
          calc
            c n (x m) ≤ c k (x m) := hc hnk _
            _ ≤ c k (x k) := (c k).monotone (hx hmk)
            _ ≤ OmegaComplete.ωSup (fun j => c j (x k))
                (fun _ _ h => hc h _) :=
              OmegaComplete.le_ωSup (fun j => c j (x k))
                (fun _ _ h => hc h _) k
            _ ≤ OmegaComplete.ωSup
                (fun r => OmegaComplete.ωSup (fun j => c j (x r))
                  (fun _ _ h => hc h _))
                (fun a b hab =>
                  OmegaComplete.ωSup_mono _ _
                    (fun j => (c j).monotone (hx hab))) :=
              OmegaComplete.le_ωSup
                (fun r => OmegaComplete.ωSup (fun j => c j (x r))
                  (fun _ _ h => hc h _))
                (fun a b hab =>
                  OmegaComplete.ωSup_mono _ _
                    (fun j => (c j).monotone (hx hab))) k
        · apply OmegaComplete.ωSup_le
          intro m
          apply OmegaComplete.ωSup_le
          intro n
          let k := max n m
          have hnk : n ≤ k := Nat.le_max_left _ _
          have hmk : m ≤ k := Nat.le_max_right _ _
          calc
            c n (x m) ≤ c k (x m) := hc hnk _
            _ ≤ c k (x k) := (c k).monotone (hx hmk)
            _ ≤ c k (OmegaComplete.ωSup x hx) :=
              (c k).monotone (OmegaComplete.le_ωSup x hx k)
            _ ≤ OmegaComplete.ωSup
                (fun j => c j (OmegaComplete.ωSup x hx))
                (fun _ _ h => hc h _) :=
              OmegaComplete.le_ωSup
                (fun j => c j (OmegaComplete.ωSup x hx))
                (fun _ _ h => hc h _) k }
  le_ωSup c hc n x :=
    OmegaComplete.le_ωSup (fun k => c k x)
      (fun _ _ h => hc h x) n
  ωSup_le c hc f hf x :=
    OmegaComplete.ωSup_le (fun n => c n x)
      (fun _ _ h => hc h x) (f x) (fun n => hf n x)

@[simp] theorem ωSup_apply (c : ℕ → OmegaMap D E) (hc : Monotone c)
    (x : D) :
    (OmegaComplete.ωSup c hc) x =
      OmegaComplete.ωSup (fun n => c n x)
        (fun _ _ h => hc h x) :=
  rfl

end FunctionSpace

end OmegaMap

end QLambda.Domain
