/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.SymmetricPowerCore
import QLambda.Domain.Presheaf.SymmetricElementInstances

/-!
# Symmetric tensor-power modules

Barrel: core permutation/average constructions, `SymmetricElement`, and
equivalence maps on symmetric powers.
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

set_option maxHeartbeats 8000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder


/-- The inherited partial countable sums on a symmetric-power fiber. -/
noncomputable def symmetricPowerFiber (A k n : ℕ) : Fiber where
  Carrier := SymmetricElement A k n
  zero := 0
  summation :=
    { HasSum := fun f x =>
        SigmaMon.ChoiSum.HasSum (fun i => (f i).val) x.val
      unique := by
        intro ι _ f x y hx hy
        apply SymmetricElement.ext
        exact SigmaMon.ChoiSum.unique hx hy
      empty := by
        convert (SigmaMon.ChoiSum.empty :
          SigmaMon.ChoiSum.HasSum
            (fun i : Empty => nomatch i)
            (0 : Superoperator n (tensorPowerDimension A k))) using 1
        rfl
      singleton := fun x => SigmaMon.ChoiSum.singleton x.val
      remove_zero := by
        intro ι _ f s x hzero
        exact SigmaMon.ChoiSum.remove_zero
          (fun i => (f i).val) s x.val
          (fun i hi => congrArg SymmetricElement.val (hzero i hi))
      reindex := by
        intro ι κ _ _ e f x
        exact SigmaMon.ChoiSum.reindex e (fun i => (f i).val) x.val
      flatten := by
        classical
        intro ι _ κ _ f x
        constructor
        · intro hflat
          rcases
              (SigmaMon.superoperatorPartialCountableSum.flatten
                (fun i j => (f i j).val) x.val).mp hflat with
            ⟨g, hrows, hsum⟩
          let G : ι → SymmetricElement A k n := fun i =>
            { val := g i
              invariant := by
                intro σ
                have hc := SigmaMon.ChoiSum.comp_left
                  (factorPermutation A k σ) (hrows i)
                have hc' : SigmaMon.ChoiSum.HasSum
                    (fun j => (f i j).val)
                    (Superoperator.comp
                      (factorPermutation A k σ) (g i)) := by
                  convert hc using 1
                  funext j
                  exact ((f i j).invariant σ).symm
                exact SigmaMon.ChoiSum.unique hc' (hrows i) }
          exact ⟨G, fun i => hrows i, hsum⟩
        · rintro ⟨g, hrows, hsum⟩
          exact
            (SigmaMon.superoperatorPartialCountableSum.flatten
              (fun i j => (f i j).val) x.val).mpr
                ⟨fun i => (g i).val, hrows, hsum⟩ }

/-- The invariant submodule representing the `k`th symmetric tensor power. -/
noncomputable def symmetricPower (A k : ℕ) : Module where
  obj n := symmetricPowerFiber A k n
  act := fun x f =>
    { val := Superoperator.comp x.val f
      invariant := by
        intro σ
        rw [Superoperator.comp_assoc, x.invariant] }
  act_zero_element := by
    intro m n f
    apply SymmetricElement.ext
    exact Superoperator.comp_zero_left f
  act_zero_map := by
    intro m n x
    apply SymmetricElement.ext
    exact Superoperator.comp_zero_right x.val
  act_id := by
    intro n x
    apply SymmetricElement.ext
    exact Superoperator.comp_identity x.val
  act_comp := by
    intro ℓ m n x f g
    apply SymmetricElement.ext
    exact (Superoperator.comp_assoc x.val f g).symm
  act_sum_element := by
    intro ι _ m n x s f h
    exact SigmaMon.ChoiSum.comp_right f h
  act_sum_map := by
    intro ι _ m n x f s h
    exact SigmaMon.ChoiSum.comp_left x.val h
  act_sum_from_one := by
    intro ι _ m x s f h
    obtain ⟨Χ, hΧ⟩ := SigmaMon.ChoiSum.comp_from_one f
      (show SigmaMon.ChoiSum.HasSum (fun i => (x i).val) s.val from h)
    refine ⟨⟨Χ, ?_⟩, hΧ⟩
    intro σ
    have hsymm (j : ι) :
        Superoperator.comp (factorPermutation A k σ)
            (Superoperator.comp (x j).val (f j)) =
          Superoperator.comp (x j).val (f j) := by
      let xj : SymmetricElement A k 1 := x j
      have hinvariant :=
        congrArg (fun Φ => Superoperator.comp Φ (f j))
          (xj.invariant σ)
      exact (Superoperator.comp_assoc _ _ _).trans hinvariant
    have hL :=
      SigmaMon.ChoiSum.comp_left (factorPermutation A k σ) hΧ
    have hfam :
        (fun j =>
          Superoperator.comp (factorPermutation A k σ)
            (Superoperator.comp (x j).val (f j))) =
          fun j => Superoperator.comp (x j).val (f j) :=
      funext hsymm
    have hL' :
        SigmaMon.ChoiSum.HasSum
          (fun j => Superoperator.comp (x j).val (f j))
          (Superoperator.comp (factorPermutation A k σ) Χ) := by
      convert hL using 1
      exact hfam.symm
    exact SigmaMon.ChoiSum.unique hL' hΧ
  act_sum_tensor_from_one := by
    intro ι _ m B x s f h
    obtain ⟨Χ, hΧ⟩ :=
      (representable (tensorPowerDimension A k)).act_sum_tensor_from_one f
        (show SigmaMon.ChoiSum.HasSum (fun i => (x i).val) s.val from h)
    refine ⟨⟨Χ, ?_⟩, hΧ⟩
    intro σ
    have hsymm (j : ι) :
        Superoperator.comp (factorPermutation A k σ)
            (Superoperator.comp (x j).val
              (Superoperator.tensor (f j)
                (Superoperator.identity B))) =
          Superoperator.comp (x j).val
            (Superoperator.tensor (f j)
              (Superoperator.identity B)) := by
      let xj : SymmetricElement A k (1 * B) := x j
      have hinvariant :=
        congrArg
          (fun Φ =>
            Superoperator.comp Φ
              (Superoperator.tensor (f j)
                (Superoperator.identity B)))
          (xj.invariant σ)
      exact (Superoperator.comp_assoc _ _ _).trans hinvariant
    have hL :=
      SigmaMon.ChoiSum.comp_left (factorPermutation A k σ) hΧ
    have hfam :
        (fun j =>
          Superoperator.comp (factorPermutation A k σ)
            (Superoperator.comp (x j).val
              (Superoperator.tensor (f j)
                (Superoperator.identity B)))) =
          fun j =>
            Superoperator.comp (x j).val
              (Superoperator.tensor (f j)
                (Superoperator.identity B)) :=
      funext hsymm
    have hL' :
        SigmaMon.ChoiSum.HasSum
          (fun j =>
            Superoperator.comp (x j).val
              (Superoperator.tensor (f j)
                (Superoperator.identity B)))
          (Superoperator.comp (factorPermutation A k σ) Χ) := by
      convert hL using 1
      exact hfam.symm
    exact SigmaMon.ChoiSum.unique hL' hΧ

/-- The averaging projection from the full tensor power onto its symmetric
fixed-point submodule. -/
noncomputable def symmetricPowerProjection (A k : ℕ) :
    Hom (representable (tensorPowerDimension A k))
      (symmetricPower A k) where
  app := fun _ x => SymmetricElement.ofAverage x
  map_zero := by
    intro n
    apply SymmetricElement.ext
    exact Superoperator.comp_zero_right _
  map_sum := by
    intro ι _ n f x h
    exact SigmaMon.ChoiSum.comp_left (symmetricAverage A k) h
  naturality := by
    intro m n x f
    apply SymmetricElement.ext
    exact Superoperator.comp_assoc _ _ _

/-- Forget the invariant proof and include a symmetric power into the full
representable tensor power. -/
def symmetricPowerInclusion (A k : ℕ) :
    Hom (symmetricPower A k)
      (representable (tensorPowerDimension A k)) where
  app := fun _ x => x.val
  map_zero := fun _ => rfl
  map_sum := fun h => h
  naturality := fun _ _ => rfl

@[simp]
theorem symmetricPowerProjection_inclusion (A k : ℕ) :
    Hom.comp (symmetricPowerProjection A k)
        (symmetricPowerInclusion A k) =
      Hom.id (symmetricPower A k) := by
  ext n x
  apply SymmetricElement.ext
  exact SymmetricElement.average_val x

theorem symmetricPowerInclusion_projection (A k : ℕ) :
    Hom.comp (symmetricPowerInclusion A k)
        (symmetricPowerProjection A k) =
      yonedaMap (symmetricAverage A k) := by
  ext n x
  rfl

/-- Extend a map defined on the symmetric power to the full representable
tensor coefficient by precomposing with the concrete averaging projector. -/
noncomputable def extendFromSymmetricPower {A B k : ℕ}
    (f : Hom (symmetricPower B k) (representable A)) :
    Hom (representable (tensorPowerDimension B k)) (representable A) :=
  Hom.comp f (symmetricPowerProjection B k)

@[simp]
theorem extendFromSymmetricPower_inclusion {A B k : ℕ}
    (f : Hom (symmetricPower B k) (representable A)) :
    Hom.comp (extendFromSymmetricPower f)
        (symmetricPowerInclusion B k) = f := by
  rw [extendFromSymmetricPower, ← Hom.comp_assoc,
    symmetricPowerProjection_inclusion, Hom.comp_id]

/-- A finite basis equivalence acts naturally on every symmetric power. -/
noncomputable def symmetricPowerEquivalenceMap {A B : ℕ}
    (e : Fin A ≃ Fin B) (k : ℕ) :
    Hom (symmetricPower A k) (symmetricPower B k) where
  app := fun _ x => SymmetricElement.mapEquivalence e x
  map_zero := by
    intro n
    apply SymmetricElement.ext
    exact Superoperator.comp_zero_right _
  map_sum := by
    intro ι _ n f x h
    exact SigmaMon.ChoiSum.comp_left
      (Superoperator.ofEquivalence (tensorTupleMapEquiv e k)) h
  naturality := by
    intro m n x f
    apply SymmetricElement.ext
    exact Superoperator.comp_assoc _ _ _

@[simp]
theorem symmetricPowerEquivalenceMap_refl (A k : ℕ) :
    symmetricPowerEquivalenceMap (Equiv.refl (Fin A)) k =
      Hom.id (symmetricPower A k) := by
  ext n x
  apply SymmetricElement.ext
  simp [symmetricPowerEquivalenceMap, SymmetricElement.mapEquivalence]

@[simp]
theorem symmetricPowerEquivalenceMap_trans {A B C : ℕ}
    (e : Fin A ≃ Fin B) (f : Fin B ≃ Fin C) (k : ℕ) :
    symmetricPowerEquivalenceMap (e.trans f) k =
      Hom.comp (symmetricPowerEquivalenceMap f k)
        (symmetricPowerEquivalenceMap e k) := by
  ext n x
  apply SymmetricElement.ext
  simp [symmetricPowerEquivalenceMap, SymmetricElement.mapEquivalence,
    Superoperator.comp_assoc]

end SuperoperatorModule

end QLambda.Domain.Presheaf
