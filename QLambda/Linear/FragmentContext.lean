/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Linear.FragmentModel
import QLambda.Domain.Presheaf.DayCoend
import QLambda.Domain.Presheaf.Comonoid

/-!
# Open fragment context objects (Route A)

Presheaf counterpart of `ContextObject` for the minimum fragment.  The
fragment admits only classical bits in unrestricted contexts, so every
unrestricted cell is interpreted by the dephasing-fixed
`classicalBitModule`. Linear `none` cells are tensor units so de Bruijn
indices remain aligned under `OSplit`.
-/

namespace QLambda.Linear
namespace FragmentContext

set_option maxHeartbeats 8000000

open Domain.Presheaf.SuperoperatorModule
open Domain.Presheaf
open DayTensor

/-- Unrestricted context object.  Route A admits only bit binders here; the
total definition uses the classical-bit carrier for every list cell, and all
public structural maps require `CtxUAllBit`. -/
noncomputable def unrestricted : List Ty → Module
  | [] => dayTensorUnit
  | _ :: Γ => dayTensor classicalBitModule (unrestricted Γ)

/-- Linear context object; absent cells are tensor units. -/
noncomputable def linear : List (Option Ty) → Module
  | [] => dayTensorUnit
  | none :: Δ => dayTensor dayTensorUnit (linear Δ)
  | some A :: Δ => dayTensor (fragmentModule A) (linear Δ)

/-- Combined context `⟦Γ⟧ ⊗ ⟦Δ⟧`. -/
noncomputable def combined (Γ : List Ty) (Δ : List (Option Ty)) : Module :=
  dayTensor (unrestricted Γ) (linear Δ)

@[simp] theorem unrestricted_nil : unrestricted [] = dayTensorUnit := rfl
@[simp] theorem linear_nil : linear [] = dayTensorUnit := rfl

theorem combined_nil_nil :
    combined [] [] = dayTensor dayTensorUnit dayTensorUnit :=
  rfl

/-- Identity on a combined context. -/
noncomputable def combinedId (Γ : List Ty) (Δ : List (Option Ty)) :
    Hom (combined Γ Δ) (combined Γ Δ) :=
  Hom.id _

/-- Bifunctorial action on combined contexts. -/
noncomputable def combinedMap {Γ Γ' : List Ty} {Δ Δ' : List (Option Ty)}
    (f : Hom (unrestricted Γ) (unrestricted Γ'))
    (g : Hom (linear Δ) (linear Δ')) :
    Hom (combined Γ Δ) (combined Γ' Δ') :=
  map f g

/-- Discard an unrestricted context whose entries are all classical bits. -/
noncomputable def unrestrictedAllBitDiscard {Γ : List Ty}
    (hΓ : CtxUAllBit Γ) : Hom (unrestricted Γ) dayTensorUnit := by
  induction Γ with
  | nil =>
      exact Hom.id dayTensorUnit
  | cons A Γ ih =>
      have hA : A = .bit := hΓ (List.Mem.head _)
      have htail : CtxUAllBit Γ := by
        intro B hm
        exact hΓ (List.Mem.tail _ hm)
      subst A
      exact Hom.comp (leftUnitor dayTensorUnit)
        (map classicalBitWeakening (ih htail))

/-- Existence of lookup from a classical-bit unrestricted context. -/
theorem unrestrictedLookup_exists {Γ : List Ty} {n : Nat} {A : Ty}
    (hΓ : CtxUAllBit Γ) (hl : Lookup Γ n A) :
    Nonempty (Hom (unrestricted Γ) (fragmentModule A)) := by
  cases Γ with
  | nil => cases hl
  | cons B Γ =>
      have hhead : B = .bit := hΓ (List.Mem.head _)
      have htail : CtxUAllBit Γ := by
        intro C hm
        exact hΓ (List.Mem.tail _ hm)
      cases n with
      | zero =>
          cases hl
          subst A
          exact ⟨Hom.comp (rightUnitor (fragmentModule .bit))
            (map classicalBitInclusion
              (unrestrictedAllBitDiscard htail))⟩
      | succ n =>
          cases hl with
          | succ hl =>
              subst B
              obtain ⟨f⟩ := unrestrictedLookup_exists htail hl
              exact ⟨Hom.comp (leftUnitor (fragmentModule A))
                (map classicalBitWeakening f)⟩
termination_by Γ.length

/-- Select an unrestricted bit variable, weakening every other bit entry. -/
noncomputable def unrestrictedLookup {Γ : List Ty} {n : Nat} {A : Ty}
    (hΓ : CtxUAllBit Γ) (hl : Lookup Γ n A) :
    Hom (unrestricted Γ) (fragmentModule A) :=
  Classical.choice (unrestrictedLookup_exists hΓ hl)

/-- Collapse the empty combined context to the Day unit. -/
noncomputable def combinedClosedCollapse :
    Hom (combined [] []) dayTensorUnit :=
  Hom.comp (leftUnitor dayTensorUnit)
    (map (Hom.id dayTensorUnit) (Hom.id dayTensorUnit))

/-- Closed observation from a Day-unit point. -/
noncomputable def closedPoint {A : Module}
    (f : Hom dayTensorUnit A) : Hom (combined [] []) A :=
  Hom.comp f combinedClosedCollapse

/-- Insert a leading `none` on the linear context. -/
noncomputable def linearConsNone (Δ : List (Option Ty)) :
    Hom (linear Δ) (linear (none :: Δ)) :=
  Hom.comp (map (Hom.id dayTensorUnit) (Hom.id (linear Δ)))
    (leftUnitorInv (linear Δ))

/-- Collapse a linear context known to contain no resources. -/
noncomputable def linearAllNoneCollapse {Δ : List (Option Ty)}
    (h : AllNone Δ) : Hom (linear Δ) dayTensorUnit := by
  induction Δ with
  | nil =>
      exact Hom.id dayTensorUnit
  | cons cell Δ ih =>
      cases cell with
      | none =>
          simp only [AllNone] at h
          exact Hom.comp (leftUnitor dayTensorUnit)
            (map (Hom.id dayTensorUnit) (ih h))
      | some A =>
          simp [AllNone] at h

/-- Existence of the projection from a singleton-used linear context.
`Nonempty` keeps the proof recursion in `Prop`; the concrete map is selected
below. -/
theorem linearOnlySomeAtProject_exists {Δ : List (Option Ty)}
    {n : Nat} {A : Ty} (hl : Lookup Δ n (some A))
    (ho : OnlySomeAt Δ n) :
    Nonempty (Hom (linear Δ) (fragmentModule A)) := by
  cases Δ with
  | nil => cases hl
  | cons cell Δ =>
      cases n with
      | zero =>
          cases cell with
          | none => cases hl
          | some B =>
              cases hl
              simp only [OnlySomeAt] at ho
              exact ⟨Hom.comp (rightUnitor (fragmentModule A))
                (map (Hom.id (fragmentModule A))
                  (linearAllNoneCollapse ho))⟩
      | succ n =>
          cases cell with
          | none =>
              cases hl with
              | succ hl =>
                  simp only [OnlySomeAt] at ho
                  obtain ⟨f⟩ := linearOnlySomeAtProject_exists hl ho
                  exact ⟨Hom.comp (leftUnitor (fragmentModule A))
                    (map (Hom.id dayTensorUnit) f)⟩
          | some B =>
              simp [OnlySomeAt] at ho
termination_by Δ.length

/-- Project the unique occupied linear cell selected by `Lookup` and
`OnlySomeAt`. -/
noncomputable def linearOnlySomeAtProject {Δ : List (Option Ty)}
    {n : Nat} {A : Ty} (hl : Lookup Δ n (some A))
    (ho : OnlySomeAt Δ n) :
    Hom (linear Δ) (fragmentModule A) :=
  Classical.choice (linearOnlySomeAtProject_exists hl ho)

/-- Canonical middle-four interchange
`(M ⊗ N) ⊗ (P ⊗ Q) → (M ⊗ P) ⊗ (N ⊗ Q)`. -/
noncomputable def tensorInterchange (M N P Q : Module) :
    Hom (dayTensor (dayTensor M N) (dayTensor P Q))
      (dayTensor (dayTensor M P) (dayTensor N Q)) :=
  Hom.comp (associatorInv M P (dayTensor N Q))
    (Hom.comp (map (Hom.id M) (associator P N Q))
      (Hom.comp
        (map (Hom.id M) (map (braiding N P) (Hom.id Q)))
        (Hom.comp (map (Hom.id M) (associatorInv N P Q))
          (associator M N (dayTensor P Q)))))

/-- Curry a morphism through the concrete Day closed structure. -/
noncomputable def dayCurry {X A N : Module}
    (f : Hom (dayTensor X A) N) :
    Hom X (dayInternalHom A N) :=
  dayClosedPresentation.closed X A N f

/-- Evaluation for the concrete Day internal hom. -/
noncomputable def dayEval (A N : Module) :
    Hom (dayTensor (dayInternalHom A N) A) N :=
  (dayClosedPresentation.closed (dayInternalHom A N) A N).symm
    (Hom.id (dayInternalHom A N))

/-- Uncurrying through Day closedness is evaluation after applying the
curried map in the first Day factor. -/
theorem dayUncurry_eq_eval_comp {X A N : Module}
    (g : Hom X (dayInternalHom A N)) :
    (dayClosedPresentation.closed X A N).symm g =
      Hom.comp (dayEval A N) (DayTensor.map g (Hom.id A)) := by
  apply DayTensor.hom_ext
  intro m n x y
  -- Both sides act on coend generators by `(g.app m x).app id y`.
  change
      ((dayClosedPresentation.closed X A N).symm g).app (m * n)
          ((DayCoend.intro X A).app x y) =
        (dayEval A N).app (m * n)
          ((DayTensor.map g (Hom.id A)).app (m * n)
            ((DayCoend.intro X A).app x y))
  have hmap := DayTensor.map_intro g (Hom.id A) x y
  rw [hmap, Hom.id_app]
  -- `closed.symm g = lift (uncurry g)` and `dayEval = lift (uncurry id)`.
  change
      DayCoend.evaluate N (DayInternalHom.uncurry g)
          ((DayCoend.intro X A).app x y) =
        DayCoend.evaluate N
          (DayInternalHom.uncurry (Hom.id (dayInternalHom A N)))
          ((DayCoend.intro (dayInternalHom A N) A).app (g.app m x) y)
  rw [DayCoend.evaluate_intro, DayCoend.evaluate_intro]
  rfl

/-- Day β: evaluating a curried Day morphism recovers the original. -/
theorem dayEval_dayCurry {X A N : Module}
    (f : Hom (dayTensor X A) N) :
    Hom.comp (dayEval A N)
      (DayTensor.map (dayCurry f) (Hom.id A)) = f := by
  rw [← dayUncurry_eq_eval_comp]
  exact (dayClosedPresentation.closed X A N).symm_apply_apply f

/-- Day η: currying an evaluated Day morphism recovers the original. -/
theorem dayCurry_dayEval {X A N : Module}
    (g : Hom X (dayInternalHom A N)) :
    dayCurry
        (Hom.comp (dayEval A N) (DayTensor.map g (Hom.id A))) =
      g := by
  rw [← dayUncurry_eq_eval_comp]
  exact (dayClosedPresentation.closed X A N).apply_symm_apply g

/-- Curry over a first-order representable domain and transport to the
specialized representable internal hom used by linear arrows. -/
noncomputable def curryFirstOrder {X N : Module} (A : ℕ)
    (f : Hom (dayTensor X (representable A)) N) :
    Hom X (internalHomRepresentable A N) :=
  Hom.comp (dayInternalHomRepresentableIso A N).hom (dayCurry f)

/-- Evaluation for the specialized representable internal hom. -/
noncomputable def evalFirstOrder (A : ℕ) (N : Module) :
    Hom (dayTensor (internalHomRepresentable A N) (representable A)) N :=
  Hom.comp (dayEval (representable A) N)
    (map (dayInternalHomRepresentableIso A N).inv
      (Hom.id (representable A)))

/-- Reorder `(U ⊗ L) ⊗ A` to `U ⊗ (A ⊗ L)`. -/
noncomputable def moveArgumentIntoLinear (U L A : Module) :
    Hom (dayTensor (dayTensor U L) A) (dayTensor U (dayTensor A L)) :=
  Hom.comp (map (Hom.id U) (braiding L A)) (associator U L A)

/-- Reorder `(U ⊗ L) ⊗ A` to `(A ⊗ U) ⊗ L`. -/
noncomputable def moveArgumentIntoUnrestricted (U L A : Module) :
    Hom (dayTensor (dayTensor U L) A) (dayTensor (dayTensor A U) L) :=
  Hom.comp (map (braiding U A) (Hom.id L))
    (Hom.comp (associatorInv U A L)
      (Hom.comp (map (Hom.id U) (braiding L A))
        (associator U L A)))

/-- Unrestricted abstraction over the genuine classical-bit carrier. -/
noncomputable def abstractUnrestricted {U L N : Module}
    (body : Hom (dayTensor (dayTensor classicalBitModule U) L) N) :
    Hom (dayTensor U L) (dayInternalHom classicalBitModule N) :=
  dayCurry
    (Hom.comp body
      (moveArgumentIntoUnrestricted U L classicalBitModule))

/-- Linear abstraction over a first-order representable domain. -/
noncomputable def abstractLinear {U L N : Module} {A : Ty}
    (hA : Ty.FirstOrder A)
    (body : Hom (dayTensor U (dayTensor (fragmentModule A) L)) N) :
    Hom (dayTensor U L)
      (internalHomRepresentable A.hilbertDim N) := by
  have e : fragmentModule A = representable hA.dimension :=
    fragmentModule_of_firstOrder hA
  have hd : hA.dimension = A.hilbertDim := by
    induction hA <;> simp_all [Ty.FirstOrder.dimension, Ty.hilbertDim]
  rw [← hd]
  rw [e] at body
  exact curryFirstOrder hA.dimension
    (Hom.comp body
      (moveArgumentIntoLinear U L (representable hA.dimension)))

private noncomputable def castHom {M N : Module} (h : M = N) : Hom M N := by
  subst N
  exact Hom.id M

private noncomputable def castHomInv {M N : Module} (h : M = N) : Hom N M := by
  subst N
  exact Hom.id M

/-- A first-order fragment object as its representing Yoneda module. -/
noncomputable def firstOrderToRep {A : Ty} (hA : Ty.FirstOrder A) :
    Hom (fragmentModule A) (representable A.hilbertDim) := by
  apply castHom
  rw [fragmentModule_of_firstOrder hA]
  congr 1

/-- Inverse representable transport for a first-order fragment object. -/
noncomputable def firstOrderFromRep {A : Ty} (hA : Ty.FirstOrder A) :
    Hom (representable A.hilbertDim) (fragmentModule A) := by
  apply castHomInv
  rw [fragmentModule_of_firstOrder hA]
  congr 1

/-- Evaluation specialized to a first-order source type. -/
noncomputable def evalFragmentFirstOrder {A : Ty}
    (hA : Ty.FirstOrder A) (N : Module) :
    Hom
      (dayTensor (internalHomRepresentable A.hilbertDim N)
        (fragmentModule A)) N :=
  Hom.comp (evalFirstOrder A.hilbertDim N)
    (map (Hom.id _) (firstOrderToRep hA))

/-- Evaluation of an unrestricted function after classicalizing its physical
term-level bit argument. -/
noncomputable def evalUnrestrictedBit (N : Module) :
    Hom
      (dayTensor (dayInternalHom classicalBitModule N)
        (fragmentModule .bit)) N :=
  Hom.comp (dayEval classicalBitModule N)
    (map (Hom.id _) bitClassicalize)

/-- Pair introduction for first-order fragment objects. -/
noncomputable def tensorIntro {A B : Ty}
    (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B) :
    Hom (dayTensor (fragmentModule A) (fragmentModule B))
      (fragmentModule (.tensor A B)) :=
  Hom.comp (firstOrderFromRep (Ty.FirstOrder.tensor hA hB))
    (Hom.comp
      (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).hom
      (map (firstOrderToRep hA) (firstOrderToRep hB)))

/-- Pair elimination for first-order fragment objects. -/
noncomputable def tensorElim {A B : Ty}
    (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B) :
    Hom (fragmentModule (.tensor A B))
      (dayTensor (fragmentModule A) (fragmentModule B)) :=
  Hom.comp (map (firstOrderFromRep hA) (firstOrderFromRep hB))
    (Hom.comp
      (dayTensorRepresentableIso A.hilbertDim B.hilbertDim).inv
      (firstOrderToRep (Ty.FirstOrder.tensor hA hB)))

/-- Apply a curried two-argument continuation to an unpacked first-order
tensor, preserving source order. -/
noncomputable def unpairApply {A B : Ty}
    (hA : Ty.FirstOrder A) (hB : Ty.FirstOrder B) (N : Module) :
    Hom
      (dayTensor (fragmentModule (.tensor A B))
        (internalHomRepresentable A.hilbertDim
          (internalHomRepresentable B.hilbertDim N)))
      N :=
  Hom.comp (evalFragmentFirstOrder hB N)
    (Hom.comp
      (map
        (evalFragmentFirstOrder hA
          (internalHomRepresentable B.hilbertDim N))
        (Hom.id (fragmentModule B)))
      (Hom.comp
        (associatorInv
          (internalHomRepresentable A.hilbertDim
            (internalHomRepresentable B.hilbertDim N))
          (fragmentModule A) (fragmentModule B))
        (Hom.comp
          (map (Hom.id _) (tensorElim hA hB))
          (braiding (fragmentModule (.tensor A B))
            (internalHomRepresentable A.hilbertDim
              (internalHomRepresentable B.hilbertDim N))))))

/-- Existence of the structural Day split induced by a linear `OSplit`. -/
theorem linearOSplit_exists {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hs : OSplit Δ Δ₁ Δ₂) :
    Nonempty (Hom (linear Δ) (dayTensor (linear Δ₁) (linear Δ₂))) := by
  induction hs with
  | nil =>
      exact ⟨leftUnitorInv dayTensorUnit⟩
  | none hs ih =>
      obtain ⟨f⟩ := ih
      exact ⟨Hom.comp
        (map (leftUnitorInv _) (leftUnitorInv _))
        (Hom.comp (leftUnitor _) (map (Hom.id dayTensorUnit) f))⟩
  | left hs ih =>
      obtain ⟨f⟩ := ih
      exact ⟨Hom.comp
        (map (Hom.id _) (leftUnitorInv _))
        (Hom.comp (associatorInv _ _ _) (map (Hom.id _) f))⟩
  | right hs ih =>
      obtain ⟨f⟩ := ih
      exact ⟨Hom.comp
        (map (leftUnitorInv _) (Hom.id _))
        (Hom.comp (associator _ _ _)
          (Hom.comp (map (braiding _ _) (Hom.id _))
            (Hom.comp (associatorInv _ _ _) (map (Hom.id _) f))))⟩

/-- Structural Day split on the underlying lists (computes without eliminating
`OSplit : Prop`). Impossible shapes return `0`. -/
noncomputable def linearOSplitLists :
    ∀ (Δ Δ₁ Δ₂ : List (Option Ty)),
      Hom (linear Δ) (dayTensor (linear Δ₁) (linear Δ₂))
  | [], [], [] => leftUnitorInv dayTensorUnit
  | none :: Δ, none :: Δ₁, none :: Δ₂ =>
      Hom.comp
        (map (leftUnitorInv _) (leftUnitorInv _))
        (Hom.comp (leftUnitor _)
          (map (Hom.id dayTensorUnit) (linearOSplitLists Δ Δ₁ Δ₂)))
  | some A :: Δ, some B :: Δ₁, none :: Δ₂ =>
      if h : A = B then
        h ▸ Hom.comp
          (map (Hom.id _) (leftUnitorInv _))
          (Hom.comp (associatorInv _ _ _)
            (map (Hom.id _) (linearOSplitLists Δ Δ₁ Δ₂)))
      else
        0
  | some A :: Δ, none :: Δ₁, some B :: Δ₂ =>
      if h : A = B then
        h ▸ Hom.comp
          (map (leftUnitorInv _) (Hom.id _))
          (Hom.comp (associator _ _ _)
            (Hom.comp (map (braiding _ _) (Hom.id _))
              (Hom.comp (associatorInv _ _ _)
                (map (Hom.id _) (linearOSplitLists Δ Δ₁ Δ₂)))))
      else
        0
  | _, _, _ => 0

/-- Structural Day split selected by an `OSplit` witness. -/
noncomputable def linearOSplit {Δ Δ₁ Δ₂ : List (Option Ty)}
    (_hs : OSplit Δ Δ₁ Δ₂) :
    Hom (linear Δ) (dayTensor (linear Δ₁) (linear Δ₂)) :=
  linearOSplitLists Δ Δ₁ Δ₂

theorem linearOSplit_nil (hs : OSplit [] [] []) :
    linearOSplit hs = leftUnitorInv dayTensorUnit :=
  rfl

/-- Physical bit copy retained only as a boundary map; unrestricted
contraction below uses `classicalBitContraction`. -/
noncomputable def bitContraction :
    Hom (representable 2) (dayTensorRepresentable 2 2) :=
  bitCopy

/-- Classical-bit contraction into the actual coend Day tensor. -/
noncomputable def bitContractionDay :
    Hom classicalBitModule
      (dayTensor classicalBitModule classicalBitModule) :=
  classicalBitContraction

/-- Bit discard available for classical weakening (Route A, not bang). -/
noncomputable def bitWeakening :
    Hom classicalBitModule dayTensorUnit :=
  classicalBitWeakening

/-- Existence of direct contraction for an all-bit unrestricted context. -/
theorem unrestrictedContraction_exists {Γ : List Ty}
    (hΓ : CtxUAllBit Γ) :
    Nonempty (Hom (unrestricted Γ)
      (dayTensor (unrestricted Γ) (unrestricted Γ))) := by
  induction Γ with
  | nil =>
      exact ⟨leftUnitorInv dayTensorUnit⟩
  | cons A Γ ih =>
      have hA : A = .bit := hΓ (List.Mem.head _)
      have htail : CtxUAllBit Γ := by
        intro B hm
        exact hΓ (List.Mem.tail _ hm)
      subst A
      obtain ⟨f⟩ := ih htail
      exact ⟨Hom.comp
        (tensorInterchange classicalBitModule classicalBitModule
          (unrestricted Γ) (unrestricted Γ))
        (map bitContractionDay f)⟩

/-- Direct contraction for an all-bit unrestricted context. -/
noncomputable def unrestrictedContractionLists :
    ∀ (Γ : List Ty),
      Hom (unrestricted Γ) (dayTensor (unrestricted Γ) (unrestricted Γ))
  | [] => leftUnitorInv dayTensorUnit
  | .bit :: Γ =>
      Hom.comp
        (tensorInterchange classicalBitModule classicalBitModule
          (unrestricted Γ) (unrestricted Γ))
        (map bitContractionDay (unrestrictedContractionLists Γ))
  | _ :: _ => 0

/-- Direct contraction for an all-bit unrestricted context. -/
noncomputable def unrestrictedContraction {Γ : List Ty}
    (_hΓ : CtxUAllBit Γ) :
    Hom (unrestricted Γ)
      (dayTensor (unrestricted Γ) (unrestricted Γ)) :=
  unrestrictedContractionLists Γ

theorem unrestrictedContraction_nil (hΓ : CtxUAllBit []) :
    unrestrictedContraction hΓ = leftUnitorInv dayTensorUnit :=
  rfl

/-- Duplicate the shared unrestricted context and split the linear context.
On empty contexts the middle-four interchange is omitted: the split is
definitionally `λ⁻¹ ⊗ λ⁻¹`, matching the Day-unit packaging used by closed
`ite` Step soundness. -/
noncomputable def combinedOSplitLists :
    ∀ (Γ : List Ty) (Δ Δ₁ Δ₂ : List (Option Ty)),
      Hom (combined Γ Δ)
        (dayTensor (combined Γ Δ₁) (combined Γ Δ₂))
  | [], [], [], [] =>
      map (leftUnitorInv dayTensorUnit) (leftUnitorInv dayTensorUnit)
  | Γ, Δ, Δ₁, Δ₂ =>
      Hom.comp
        (tensorInterchange (unrestricted Γ) (unrestricted Γ)
          (linear Δ₁) (linear Δ₂))
        (map (unrestrictedContractionLists Γ) (linearOSplitLists Δ Δ₁ Δ₂))

/-- Duplicate the shared unrestricted context and split the linear context. -/
noncomputable def combinedOSplit {Γ : List Ty}
    {Δ Δ₁ Δ₂ : List (Option Ty)} (_hΓ : CtxUAllBit Γ)
    (_hs : OSplit Δ Δ₁ Δ₂) :
    Hom (combined Γ Δ)
      (dayTensor (combined Γ Δ₁) (combined Γ Δ₂)) :=
  combinedOSplitLists Γ Δ Δ₁ Δ₂

/-- Empty combined split is the Day-unit pairing `λ⁻¹ ⊗ λ⁻¹`. -/
theorem combinedOSplit_nil (hΓ : CtxUAllBit []) (hs : OSplit [] [] []) :
    combinedOSplit hΓ hs =
      map (leftUnitorInv dayTensorUnit) (leftUnitorInv dayTensorUnit) :=
  rfl

/-- Select an unrestricted bit variable from a combined context. -/
noncomputable def combinedLookupUnrestricted {Γ : List Ty}
    {Δ : List (Option Ty)} {n : Nat} {A : Ty}
    (hΓ : CtxUAllBit Γ) (hl : Lookup Γ n A) (hΔ : AllNone Δ) :
    Hom (combined Γ Δ) (fragmentModule A) :=
  Hom.comp (rightUnitor (fragmentModule A))
    (map (unrestrictedLookup hΓ hl) (linearAllNoneCollapse hΔ))

/-- Select the unique occupied linear variable from a combined context. -/
noncomputable def combinedLookupLinear {Γ : List Ty}
    {Δ : List (Option Ty)} {n : Nat} {A : Ty}
    (hΓ : CtxUAllBit Γ) (hl : Lookup Δ n (some A))
    (ho : OnlySomeAt Δ n) :
    Hom (combined Γ Δ) (fragmentModule A) :=
  Hom.comp (leftUnitor (fragmentModule A))
    (map (unrestrictedAllBitDiscard hΓ)
      (linearOnlySomeAtProject hl ho))

/-- Discard a combined context with an all-bit unrestricted part and no
occupied linear cells. -/
noncomputable def combinedAllDiscard {Γ : List Ty}
    {Δ : List (Option Ty)} (hΓ : CtxUAllBit Γ) (hΔ : AllNone Δ) :
    Hom (combined Γ Δ) dayTensorUnit :=
  Hom.comp (leftUnitor dayTensorUnit)
    (map (unrestrictedAllBitDiscard hΓ) (linearAllNoneCollapse hΔ))

/-- Extend a point at the Day unit to a constant map on a discardable
combined context. -/
noncomputable def combinedPoint {Γ : List Ty}
    {Δ : List (Option Ty)} {A : Module}
    (hΓ : CtxUAllBit Γ) (hΔ : AllNone Δ)
    (f : Hom dayTensorUnit A) :
    Hom (combined Γ Δ) A :=
  Hom.comp f (combinedAllDiscard hΓ hΔ)

/-- Structural context maps do not depend on proof witnesses. -/
theorem linearAllNoneCollapse_proof_independent {Δ : List (Option Ty)}
    (h h' : AllNone Δ) :
    linearAllNoneCollapse h = linearAllNoneCollapse h' := by
  congr

theorem unrestrictedAllBitDiscard_proof_independent {Γ : List Ty}
    (hΓ hΓ' : CtxUAllBit Γ) :
    unrestrictedAllBitDiscard hΓ = unrestrictedAllBitDiscard hΓ' := by
  congr

theorem combinedAllDiscard_proof_independent {Γ : List Ty}
    {Δ : List (Option Ty)} (hΓ hΓ' : CtxUAllBit Γ) (hΔ hΔ' : AllNone Δ) :
    combinedAllDiscard hΓ hΔ = combinedAllDiscard hΓ' hΔ' := by
  congr

theorem linearOnlySomeAtProject_proof_independent
    {Δ : List (Option Ty)} {n : Nat} {A : Ty}
    (hl hl' : Lookup Δ n (some A)) (ho ho' : OnlySomeAt Δ n) :
    linearOnlySomeAtProject hl ho =
      linearOnlySomeAtProject hl' ho' := by
  congr

theorem linearOSplit_proof_independent {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hs hs' : OSplit Δ Δ₁ Δ₂) :
    linearOSplit hs = linearOSplit hs' := by
  congr

theorem unrestrictedLookup_proof_independent
    {Γ : List Ty} {n : Nat} {A : Ty}
    (hΓ hΓ' : CtxUAllBit Γ) (hl hl' : Lookup Γ n A) :
    unrestrictedLookup hΓ hl = unrestrictedLookup hΓ' hl' := by
  congr

theorem combinedOSplit_proof_independent {Γ : List Ty}
    {Δ Δ₁ Δ₂ : List (Option Ty)}
    (hΓ hΓ' : CtxUAllBit Γ) (hs hs' : OSplit Δ Δ₁ Δ₂) :
    combinedOSplit hΓ hs = combinedOSplit hΓ' hs' := by
  congr

/-- Classical-bit contraction satisfies the left counit law in the genuine
Day tensor. -/
theorem classicalBitContraction_left_counit :
    Hom.comp (leftUnitor classicalBitModule)
        (Hom.comp
          (map classicalBitWeakening (Hom.id classicalBitModule))
          classicalBitContraction) =
      Hom.id classicalBitModule := by
  apply Hom.ext
  intro n x
  rcases x with ⟨x, hx⟩
  change
    (leftUnitor classicalBitModule).app n
      ((map classicalBitWeakening (Hom.id classicalBitModule)).app n
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator x))) =
      ⟨x, hx⟩
  rw [(map classicalBitWeakening (Hom.id classicalBitModule)).naturality]
  rw [map_intro, Hom.id_app]
  rw [(leftUnitor classicalBitModule).naturality]
  change
    classicalBitModule.act
      ((leftUnitor classicalBitModule).app (2 * 2)
        ((DayCoend.intro dayTensorUnit classicalBitModule).app
          (Superoperator.comp SigmaMon.ChoiSum.discardTwo
            bitDephaseSuperoperator)
          classicalBitGeneric))
      (Superoperator.comp bitCopySuperoperator x) =
    ⟨x, hx⟩
  rw [leftUnitor_intro]
  apply Subtype.ext
  simp only [classicalBitModule, classicalBitGeneric]
  rw [← Superoperator.comp_assoc]
  rw [Superoperator.comp_assoc
    (Superoperator.comp
      (Superoperator.tensorLeftUnitor 2)
      (Superoperator.tensor
        (Superoperator.comp SigmaMon.ChoiSum.discardTwo
          bitDephaseSuperoperator)
        (Superoperator.identity 2)))
    bitCopySuperoperator x]
  rw [Superoperator.comp_assoc]
  have hc :
      Superoperator.comp bitDephaseSuperoperator
        (Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorLeftUnitor 2)
            (Superoperator.tensor
              (Superoperator.comp SigmaMon.ChoiSum.discardTwo
                bitDephaseSuperoperator)
              (Superoperator.identity 2)))
          bitCopySuperoperator) =
        bitDephaseSuperoperator := by
    simpa only [Superoperator.comp_assoc] using
      bitClassicalLeftCounitChannel
  rw [hc]
  exact hx

/-- Classical-bit contraction satisfies the right counit law. -/
theorem classicalBitContraction_right_counit :
    Hom.comp (rightUnitor classicalBitModule)
        (Hom.comp
          (map (Hom.id classicalBitModule) classicalBitWeakening)
          classicalBitContraction) =
      Hom.id classicalBitModule := by
  apply Hom.ext
  intro n x
  rcases x with ⟨x, hx⟩
  change
    (rightUnitor classicalBitModule).app n
      ((map (Hom.id classicalBitModule) classicalBitWeakening).app n
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator x))) =
      ⟨x, hx⟩
  rw [(map (Hom.id classicalBitModule) classicalBitWeakening).naturality]
  rw [map_intro, Hom.id_app]
  rw [(rightUnitor classicalBitModule).naturality]
  change
    classicalBitModule.act
      ((rightUnitor classicalBitModule).app (2 * 2)
        ((DayCoend.intro classicalBitModule dayTensorUnit).app
          classicalBitGeneric
          (Superoperator.comp SigmaMon.ChoiSum.discardTwo
            bitDephaseSuperoperator)))
      (Superoperator.comp bitCopySuperoperator x) =
    ⟨x, hx⟩
  rw [rightUnitor_intro]
  apply Subtype.ext
  simp only [classicalBitModule, classicalBitGeneric]
  rw [← Superoperator.comp_assoc]
  rw [Superoperator.comp_assoc
    (Superoperator.comp
      (Superoperator.tensorRightUnitor 2)
      (Superoperator.tensor
        (Superoperator.identity 2)
        (Superoperator.comp SigmaMon.ChoiSum.discardTwo
          bitDephaseSuperoperator)))
    bitCopySuperoperator x]
  rw [Superoperator.comp_assoc]
  have hc :
      Superoperator.comp bitDephaseSuperoperator
        (Superoperator.comp
          (Superoperator.comp
            (Superoperator.tensorRightUnitor 2)
            (Superoperator.tensor
              (Superoperator.identity 2)
              (Superoperator.comp SigmaMon.ChoiSum.discardTwo
                bitDephaseSuperoperator)))
          bitCopySuperoperator) =
        bitDephaseSuperoperator := by
    simpa only [Superoperator.comp_assoc] using
      bitClassicalRightCounitChannel
  rw [hc]
  exact hx

/-- Classical-bit contraction is invariant under Day braiding. -/
theorem classicalBitContraction_cocommutative :
    Hom.comp (braiding classicalBitModule classicalBitModule)
        classicalBitContraction =
      classicalBitContraction := by
  apply Hom.ext
  intro n x
  rcases x with ⟨x, hx⟩
  change
    (braiding classicalBitModule classicalBitModule).app n
      ((dayTensor classicalBitModule classicalBitModule).act
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        (Superoperator.comp bitCopySuperoperator x)) =
      (dayTensor classicalBitModule classicalBitModule).act
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        (Superoperator.comp bitCopySuperoperator x)
  rw [(braiding classicalBitModule classicalBitModule).naturality]
  rw [braiding_intro]
  rw [(dayTensor classicalBitModule classicalBitModule).act_comp]
  congr 1
  rw [Superoperator.comp_assoc]
  exact congrArg (fun z => Superoperator.comp z x)
    bitCocommutativityLeft_eq_copy

/-- Classical-bit contraction is coassociative in the genuine Day tensor. -/
theorem classicalBitContraction_coassociative :
    Hom.comp
        (associator classicalBitModule classicalBitModule classicalBitModule)
        (Hom.comp
          (map classicalBitContraction (Hom.id classicalBitModule))
          classicalBitContraction) =
      Hom.comp
        (map (Hom.id classicalBitModule) classicalBitContraction)
        classicalBitContraction := by
  apply Hom.ext
  intro n x
  rcases x with ⟨x, hx⟩
  change
    (associator classicalBitModule classicalBitModule
        classicalBitModule).app n
      ((map classicalBitContraction (Hom.id classicalBitModule)).app n
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator x))) =
      (map (Hom.id classicalBitModule) classicalBitContraction).app n
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator x))
  rw [(map classicalBitContraction (Hom.id classicalBitModule)).naturality,
    (map (Hom.id classicalBitModule) classicalBitContraction).naturality,
    map_intro, map_intro]
  -- Goal now has `classicalBitContraction.app 2 classicalBitGeneric` on each side.
  change
    (associator classicalBitModule classicalBitModule
        classicalBitModule).app n
      ((dayTensor
            (dayTensor classicalBitModule classicalBitModule)
            classicalBitModule).act
        ((DayCoend.intro
            (dayTensor classicalBitModule classicalBitModule)
            classicalBitModule).app
          ((dayTensor classicalBitModule classicalBitModule).act
            ((DayCoend.intro classicalBitModule classicalBitModule).app
              classicalBitGeneric classicalBitGeneric)
            (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator))
          classicalBitGeneric)
        (Superoperator.comp bitCopySuperoperator x)) =
      (dayTensor classicalBitModule
          (dayTensor classicalBitModule classicalBitModule)).act
        ((DayCoend.intro classicalBitModule
            (dayTensor classicalBitModule classicalBitModule)).app
          classicalBitGeneric
          ((dayTensor classicalBitModule classicalBitModule).act
            ((DayCoend.intro classicalBitModule classicalBitModule).app
              classicalBitGeneric classicalBitGeneric)
            (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)))
        (Superoperator.comp bitCopySuperoperator x)
  -- Reassociate nested `act`/`intro` via bilinear naturality.
  have hleft_gen :
      (DayCoend.intro
          (dayTensor classicalBitModule classicalBitModule)
          classicalBitModule).app
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator))
        classicalBitGeneric =
      (dayTensor
          (dayTensor classicalBitModule classicalBitModule)
          classicalBitModule).act
        ((DayCoend.intro
            (dayTensor classicalBitModule classicalBitModule)
            classicalBitModule).app
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          classicalBitGeneric)
        (Superoperator.tensor
          (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)
          (Superoperator.identity 2)) := by
    have h :=
      (DayCoend.intro
          (dayTensor classicalBitModule classicalBitModule)
          classicalBitModule).naturality
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        classicalBitGeneric
        (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)
        (Superoperator.identity 2)
    simpa [classicalBitModule.act_id] using h
  have hright_gen :
      (DayCoend.intro classicalBitModule
          (dayTensor classicalBitModule classicalBitModule)).app
        classicalBitGeneric
        ((dayTensor classicalBitModule classicalBitModule).act
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric)
          (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)) =
      (dayTensor classicalBitModule
          (dayTensor classicalBitModule classicalBitModule)).act
        ((DayCoend.intro classicalBitModule
            (dayTensor classicalBitModule classicalBitModule)).app
          classicalBitGeneric
          ((DayCoend.intro classicalBitModule classicalBitModule).app
            classicalBitGeneric classicalBitGeneric))
        (Superoperator.tensor (Superoperator.identity 2)
          (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)) := by
    have h :=
      (DayCoend.intro classicalBitModule
          (dayTensor classicalBitModule classicalBitModule)).naturality
        classicalBitGeneric
        ((DayCoend.intro classicalBitModule classicalBitModule).app
          classicalBitGeneric classicalBitGeneric)
        (Superoperator.identity 2)
        (Superoperator.comp bitCopySuperoperator bitDephaseSuperoperator)
    simpa [classicalBitModule.act_id] using h
  rw [hleft_gen, hright_gen]
  rw [(dayTensor
      (dayTensor classicalBitModule classicalBitModule)
      classicalBitModule).act_comp,
    (dayTensor classicalBitModule
      (dayTensor classicalBitModule classicalBitModule)).act_comp]
  rw [(associator classicalBitModule classicalBitModule
      classicalBitModule).naturality]
  have happ :=
    associator_intro_intro
      (M := classicalBitModule) (N := classicalBitModule)
      (P := classicalBitModule)
      classicalBitGeneric classicalBitGeneric classicalBitGeneric
  rw [happ]
  rw [(dayTensor classicalBitModule
      (dayTensor classicalBitModule classicalBitModule)).act_comp]
  congr 1
  -- Channels: associator ∘ ((C∘D)⊗id) ∘ C  =  (id⊗(C∘D)) ∘ C
  have hchan :=
    congrArg (fun z : Superoperator 2 8 => Superoperator.comp z x)
      bitCoassocLeft_eq_right
  -- Unfold the named composites and reassociate past `x`.
  simp only [bitCoassocLeft, bitCoassocLeftPre, bitCoassocRight,
    Superoperator.comp_assoc] at hchan ⊢
  exact hchan

/-- OSplit preserves linear context lengths (structural coherence premise). -/
theorem oSplit_lengths {Δ Δ₁ Δ₂ : List (Option Ty)}
    (h : OSplit Δ Δ₁ Δ₂) :
    Δ₁.length = Δ.length ∧ Δ₂.length = Δ.length :=
  OSplit.lengths h

/-- Route A fragment contexts exist without a global bang. -/
theorem routeA_fragment_context_acceptance :
    (unrestricted [] = dayTensorUnit) ∧
    (linear [] = dayTensorUnit) ∧
    (∃ γ : Hom classicalBitModule
        (dayTensor classicalBitModule classicalBitModule),
      γ = classicalBitContraction) ∧
    (∃ δ : Hom classicalBitModule dayTensorUnit,
      δ = classicalBitWeakening) ∧
    (∀ Γ Δ, combined Γ Δ = dayTensor (unrestricted Γ) (linear Δ)) :=
  ⟨rfl, rfl, ⟨classicalBitContraction, rfl⟩,
    ⟨classicalBitWeakening, rfl⟩, fun _ _ => rfl⟩

/-- The dephasing-fixed classical bit is a commutative Day comonoid. -/
noncomputable def classicalBitComonoid :
    Domain.Presheaf.SuperoperatorModule.Comonoid where
  carrier := classicalBitModule
  counit := classicalBitWeakening
  comult := classicalBitContraction
  left_counit := classicalBitContraction_left_counit
  right_counit := classicalBitContraction_right_counit
  coassociative := classicalBitContraction_coassociative
  cocommutative := classicalBitContraction_cocommutative

end FragmentContext
end QLambda.Linear
