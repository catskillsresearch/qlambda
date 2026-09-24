/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.RepresentableBipolar.Surjectivity

/-!
# Classical monoidal and additive connectives (plan gate 2)

Gate progress (`classical-omega-category`): **partial — honest slice**.

## Proved `ClassicalObject`s
* `unitClassicalObject` — `I = y(1)`
* `qubitClassicalObject` — `y(2)` (quantum qubit)
* `bitClassicalObject` — classical bit as Yoneda biproduct `y(1+1)`, transported
  along `additiveBitIso : additiveBitModule ≅ y(2)`; injections `bitInl` / `bitInr`
* `classicalRepresentableTensor A B` — `y(A) ⊗ y(B) ≅ y(A*B)`
* `classicalDoubleDualObject C` — `¬¬C` for classical `C`
* `classicalTensorOf` / `classicalTensorRepresentable` — `¬¬(M ⊗ N)` when the
  raw Day tensor is already classical / representable

## Proved lemmas (not packaged as `ClassicalObject`)
* `dayTensorDoubleDualIso` — `M ⊗ N ≅ ¬¬M ⊗ ¬¬N` for classical `M,N`
* `additiveBitIso` / `bitInl` / `bitInr` — Yoneda `I ⊕ I = y(1+1) ≅ y(2)`
* `additiveProductDoubleDualInv` / `additiveProduct_inv_hom` — one triangle of
  pointwise-product reflexivity (`inv ∘ unit = id`); the reverse triangle is open
  (effect-sum / TNI obstruction blocks treating `additiveProduct I I` as `y(2)`)

## Deliberately omitted (not claimed)
* Polymorphic `classicalTensor M N` as `¬¬(M ⊗ N)` for arbitrary classical factors
* `classicalAdditiveProduct` as a `ClassicalObject` (needs product `hom_inv`)
* Pointwise `additiveProduct I I ≅ y(2)` as Module Iso (false under TNI)
* Representable internal-hom ClassicalObject beyond dual packaging
* Distributivity

## Still missing for full gate 2
* Product `hom_inv` / dualization `¬¬(M × N) ≅ ¬¬M × ¬¬N`
* Raw Day-tensor classicality for non-representable classical factors
* Scott continuity of monoidal operations / Hom ωCPO on `ClassicalObject`
-/

namespace QLambda.Domain.Presheaf

namespace SuperoperatorModule

/-! ## Transport along module isomorphisms -/

/-- Transport canonical reflexivity along a module isomorphism. -/
noncomputable def CanonicalReflexivity.transport {M N : Module}
    (e : Iso M N) (h : CanonicalReflexivity M) :
    CanonicalReflexivity N where
  inv :=
    Hom.comp e.hom
      (Hom.comp h.inv (DayNegation.map (DayNegation.map e.inv)))
  inv_hom := by
    apply Hom.ext
    intro n x
    have hnat := congrArg (fun f : Hom _ _ => f.app n x)
      (DayNegation.unit_natural e.inv)
    change
      ((DayNegation.unit M).app n (e.inv.app n x)) =
        ((DayNegation.map (DayNegation.map e.inv)).app n
          ((DayNegation.unit N).app n x)) at hnat
    have h2 := congrArg (fun z => e.hom.app n (h.inv.app n z)) hnat.symm
    have h3 := congrArg (e.hom.app n)
      (congrArg (fun f : Hom M M => f.app n (e.inv.app n x)) h.inv_hom)
    have h4 := congrArg (fun f : Hom N N => f.app n x) e.hom_inv
    exact (h2.trans h3).trans h4
  hom_inv := by
    apply Hom.ext
    intro n x
    have hnat := congrArg
      (fun f : Hom _ _ => f.app n
        (h.inv.app n ((DayNegation.map (DayNegation.map e.inv)).app n x)))
      (DayNegation.unit_natural e.hom)
    change
      ((DayNegation.unit N).app n
          (e.hom.app n
            (h.inv.app n
              ((DayNegation.map (DayNegation.map e.inv)).app n x)))) =
        ((DayNegation.map (DayNegation.map e.hom)).app n
          ((DayNegation.unit M).app n
            (h.inv.app n
              ((DayNegation.map (DayNegation.map e.inv)).app n x)))) at hnat
    have h2 := congrArg
      (fun z => (DayNegation.map (DayNegation.map e.hom)).app n z)
      (congrArg (fun f : Hom _ _ => f.app n
        ((DayNegation.map (DayNegation.map e.inv)).app n x)) h.hom_inv)
    have h3 :
        Hom.comp (DayNegation.map (DayNegation.map e.hom))
          (DayNegation.map (DayNegation.map e.inv)) =
          Hom.id (DayNegation.neg (DayNegation.neg N)) := by
      rw [← DayNegation.map_comp, ← DayNegation.map_comp, e.hom_inv,
        DayNegation.map_id, DayNegation.map_id]
    have h3app := congrArg (fun f : Hom _ _ => f.app n x) h3
    exact hnat.trans (h2.trans h3app)

/-- Transport a pseudo-basis along a module isomorphism. -/
noncomputable def PseudoBasis.transport {M N : Module}
    (e : Iso M N) (b : PseudoBasis M) : PseudoBasis N where
  Index := b.Index
  countableIndex := b.countableIndex
  coeff := b.coeff
  ket := fun i => Hom.comp e.hom (b.ket i)
  bra := fun i => Hom.comp (b.bra i) e.inv
  resolves := by
    have h := b.resolves
    have hreindex :
        Hom.HasSum
          (fun i => Hom.comp e.hom
            (Hom.comp (Hom.comp (b.ket i) (b.bra i)) e.inv))
          (Hom.comp e.hom (Hom.comp (Hom.id M) e.inv)) :=
      Hom.hasSum_comp_left e.hom (Hom.hasSum_comp_right e.inv h)
    simp only [Hom.comp_assoc, Hom.id_comp, e.hom_inv] at hreindex
    convert hreindex using 1
    funext i
    simp only [Hom.comp_assoc]

/-- Extract the underlying `CanonicalReflexivity` witness from a classical object. -/
noncomputable def ClassicalObject.toCanonicalReflexivity
    (C : ClassicalObject DayNegation.data) :
    CanonicalReflexivity C.module where
  inv := by
    simpa [DayNegation.data, NegationData.doubleDual] using C.reflexive.inv
  hom_inv := by
    have h := C.reflexive.hom_inv
    have hc : C.reflexive.hom = DayNegation.unit C.module := C.canonical
    simp only [DayNegation.data, NegationData.doubleDual] at h ⊢
    convert h
    · exact hc.symm
    · rfl
  inv_hom := by
    have h := C.reflexive.inv_hom
    have hc : C.reflexive.hom = DayNegation.unit C.module := C.canonical
    simp only [DayNegation.data, NegationData.doubleDual] at h ⊢
    convert h
    · rfl
    · exact hc.symm

/-- Package a module with an exhibited basis and reflexivity as a classical object. -/
noncomputable def classicalObjectOf
    (M : Module) (b : PseudoBasis M) (h : CanonicalReflexivity M) :
    ClassicalObject DayNegation.data where
  module := M
  basis := b
  reflexive := h.iso
  canonical := rfl

/-- Rebuild a classical object on an isomorphic module. -/
noncomputable def ClassicalObject.ofIso
    (C : ClassicalObject DayNegation.data) {M : Module}
    (e : Iso C.module M) :
    ClassicalObject DayNegation.data :=
  classicalObjectOf M (PseudoBasis.transport e C.basis)
    (CanonicalReflexivity.transport e C.toCanonicalReflexivity)

/-- Flip an isomorphism. -/
noncomputable def Iso.symm {M N : Module} (e : Iso M N) : Iso N M where
  hom := e.inv
  inv := e.hom
  hom_inv := e.inv_hom
  inv_hom := e.hom_inv

/-! ## Source primitives -/

/-- Tensor unit `I = y(1)` as a classical object. -/
noncomputable def unitClassicalObject :
    ClassicalObject DayNegation.data :=
  representableClassicalObject 1 (by decide)

/-- Qubit object `y(2)` as a classical object.

Distinct from the classical bit: arXiv has `⟦Qubit⟧ = y(2)` and
`⟦Bit⟧ = I ⊕ I`. -/
noncomputable def qubitClassicalObject :
    ClassicalObject DayNegation.data :=
  representableClassicalObject 2 (by decide)

/-! ## Representable classical tensor -/

/-- Day tensor of positive representables is classical via `y(A) ⊗ y(B) ≅ y(A*B)`. -/
noncomputable def classicalRepresentableTensor
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ClassicalObject DayNegation.data :=
  let R := representableClassicalObject (A * B) (Nat.mul_pos hA hB)
  let e := dayTensorRepresentableIso A B
  ClassicalObject.ofIso R e.symm

theorem classicalRepresentableTensor_module
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (classicalRepresentableTensor A B hA hB).module =
      dayTensor (representable A) (representable B) :=
  rfl

/-- Underlying comparison `y(A) ⊗ y(B) → y(A*B)`. -/
noncomputable def classicalRepresentableTensor_to_representable
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ClassicalObject.Hom
      (classicalRepresentableTensor A B hA hB)
      (representableClassicalObject (A * B) (Nat.mul_pos hA hB)) :=
  (dayTensorRepresentableIso A B).hom

/-- Inverse comparison `y(A*B) → y(A) ⊗ y(B)`. -/
noncomputable def classicalRepresentableTensor_of_representable
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ClassicalObject.Hom
      (representableClassicalObject (A * B) (Nat.mul_pos hA hB))
      (classicalRepresentableTensor A B hA hB) :=
  (dayTensorRepresentableIso A B).inv

/-! ## Double-dual reflexivity -/

/-- If `¬X` is reflexive, then so is `¬¬X`. -/
noncomputable def doubleDualReflexivity_of_neg
    {X : Module} (h : CanonicalReflexivity (DayNegation.neg X)) :
    CanonicalReflexivity (DayNegation.neg (DayNegation.neg X)) where
  inv := DayNegation.map (DayNegation.unit (DayNegation.neg X))
  inv_hom := DayNegation.map_unit_unit_neg (DayNegation.neg X)
  hom_inv := by
    have hmap :
        Hom.comp (DayNegation.map h.inv)
          (DayNegation.map (DayNegation.unit (DayNegation.neg X))) =
          Hom.id
            (DayNegation.neg
              (DayNegation.neg (DayNegation.neg (DayNegation.neg X)))) := by
      rw [← DayNegation.map_comp, h.hom_inv, DayNegation.map_id]
    have hre := DayNegation.map_unit_unit_neg (DayNegation.neg X)
    have hunit :
        DayNegation.unit (DayNegation.neg (DayNegation.neg X)) =
          DayNegation.map h.inv := by
      calc
        DayNegation.unit (DayNegation.neg (DayNegation.neg X))
          = Hom.comp
              (Hom.comp (DayNegation.map h.inv)
                (DayNegation.map (DayNegation.unit (DayNegation.neg X))))
              (DayNegation.unit (DayNegation.neg (DayNegation.neg X))) := by
                rw [hmap, Hom.id_comp]
        _ = Hom.comp (DayNegation.map h.inv)
              (Hom.comp (DayNegation.map (DayNegation.unit (DayNegation.neg X)))
                (DayNegation.unit (DayNegation.neg (DayNegation.neg X)))) := by
                rw [Hom.comp_assoc]
        _ = Hom.comp (DayNegation.map h.inv)
              (Hom.id (DayNegation.neg (DayNegation.neg X))) := by
                rw [hre]
        _ = DayNegation.map h.inv := Hom.comp_id _
    change Hom.comp (DayNegation.unit (DayNegation.neg (DayNegation.neg X)))
        (DayNegation.map (DayNegation.unit (DayNegation.neg X))) =
      Hom.id _
    rw [hunit]
    exact hmap

/-- Negation of a classical object is canonically reflexive (triple negation). -/
noncomputable def classicalNegReflexivity
    (C : ClassicalObject DayNegation.data) :
    CanonicalReflexivity (DayNegation.neg C.module) where
  inv := DayNegation.map (DayNegation.unit C.module)
  inv_hom := DayNegation.map_unit_unit_neg C.module
  hom_inv := by
    have hC := C.toCanonicalReflexivity
    have hmap :
        Hom.comp (DayNegation.map hC.inv)
          (DayNegation.map (DayNegation.unit C.module)) =
          Hom.id (DayNegation.neg (DayNegation.neg (DayNegation.neg C.module))) := by
      rw [← DayNegation.map_comp, hC.hom_inv, DayNegation.map_id]
    have hre := DayNegation.map_unit_unit_neg C.module
    have hunit :
        DayNegation.unit (DayNegation.neg C.module) =
          DayNegation.map hC.inv := by
      calc
        DayNegation.unit (DayNegation.neg C.module)
          = Hom.comp
              (Hom.comp (DayNegation.map hC.inv)
                (DayNegation.map (DayNegation.unit C.module)))
              (DayNegation.unit (DayNegation.neg C.module)) := by
                rw [hmap, Hom.id_comp]
        _ = Hom.comp (DayNegation.map hC.inv)
              (Hom.comp (DayNegation.map (DayNegation.unit C.module))
                (DayNegation.unit (DayNegation.neg C.module))) := by
                rw [Hom.comp_assoc]
        _ = Hom.comp (DayNegation.map hC.inv)
              (Hom.id (DayNegation.neg C.module)) := by rw [hre]
        _ = DayNegation.map hC.inv := Hom.comp_id _
    change Hom.comp (DayNegation.unit (DayNegation.neg C.module))
        (DayNegation.map (DayNegation.unit C.module)) =
      Hom.id _
    rw [hunit]
    exact hmap

/-- Double dual of a classical module is reflexive. -/
noncomputable def classicalDoubleDualReflexivity
    (C : ClassicalObject DayNegation.data) :
    CanonicalReflexivity (DayNegation.neg (DayNegation.neg C.module)) :=
  doubleDualReflexivity_of_neg (classicalNegReflexivity C)

/-- The double dual of a classical object, as a classical object. -/
noncomputable def classicalDoubleDualObject
    (C : ClassicalObject DayNegation.data) :
    ClassicalObject DayNegation.data :=
  classicalObjectOf
    (DayNegation.neg (DayNegation.neg C.module))
    (PseudoBasis.transport
      { hom := DayNegation.unit C.module
        inv := C.toCanonicalReflexivity.inv
        hom_inv := C.toCanonicalReflexivity.hom_inv
        inv_hom := C.toCanonicalReflexivity.inv_hom }
      C.basis)
    (classicalDoubleDualReflexivity C)

/-! ## Double-dualized classical tensor (proved cases) -/

/-- Iso `M ⊗ N ≅ ¬¬M ⊗ ¬¬N` for classical `M, N`. -/
noncomputable def dayTensorDoubleDualIso
    (M N : ClassicalObject DayNegation.data) :
    Iso (dayTensor M.module N.module)
      (dayTensor
        (DayNegation.neg (DayNegation.neg M.module))
        (DayNegation.neg (DayNegation.neg N.module))) where
  hom := DayTensor.map (DayNegation.unit M.module) (DayNegation.unit N.module)
  inv :=
    DayTensor.map M.toCanonicalReflexivity.inv N.toCanonicalReflexivity.inv
  hom_inv := by
    rw [← DayTensor.map_comp, M.toCanonicalReflexivity.hom_inv,
      N.toCanonicalReflexivity.hom_inv, DayTensor.map_id]
  inv_hom := by
    rw [← DayTensor.map_comp, M.toCanonicalReflexivity.inv_hom,
      N.toCanonicalReflexivity.inv_hom, DayTensor.map_id]

/-- Module of the ¬¬ packaging `¬¬(M ⊗ N)` (not itself a `ClassicalObject`
without a reflexivity witness for the raw tensor or its double dual). -/
noncomputable abbrev classicalTensorModule
    (M N : ClassicalObject DayNegation.data) : Module :=
  DayNegation.neg (DayNegation.neg (dayTensor M.module N.module))

/-- Classical ¬¬ tensor from an exhibited classicality witness for the raw Day
tensor. -/
noncomputable def classicalTensorOf
    (M N : ClassicalObject DayNegation.data)
    (b : PseudoBasis (dayTensor M.module N.module))
    (h : CanonicalReflexivity (dayTensor M.module N.module)) :
    ClassicalObject DayNegation.data :=
  classicalDoubleDualObject (classicalObjectOf _ b h)

/-- Classical ¬¬ tensor of positive representables.

Since `y(A) ⊗ y(B)` is already classical (`classicalRepresentableTensor`),
this is the double dual of that classical object — a proved `ClassicalObject`
exhibiting the ¬¬ packaging on the representable fragment. -/
noncomputable def classicalTensorRepresentable
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ClassicalObject DayNegation.data :=
  let T := classicalRepresentableTensor A B hA hB
  classicalTensorOf
    (representableClassicalObject A hA)
    (representableClassicalObject B hB)
    T.basis T.toCanonicalReflexivity

/-! ## Pointwise additive product scaffolding -/

/-- Left injection into a pointwise additive product. -/
noncomputable def additiveInl (M N : Module) :
    Hom M (additiveProduct M N) :=
  additivePair (Hom.id M) 0

/-- Right injection into a pointwise additive product. -/
noncomputable def additiveInr (M N : Module) :
    Hom N (additiveProduct M N) :=
  additivePair 0 (Hom.id N)

@[simp]
theorem additiveFst_inl (M N : Module) :
    Hom.comp (additiveFst M N) (additiveInl M N) = Hom.id M := by
  simp [additiveInl]

@[simp]
theorem additiveSnd_inr (M N : Module) :
    Hom.comp (additiveSnd M N) (additiveInr M N) = Hom.id N := by
  simp [additiveInr]

@[simp]
theorem additiveSnd_inl (M N : Module) :
    Hom.comp (additiveSnd M N) (additiveInl M N) = 0 := by
  simp [additiveInl]

@[simp]
theorem additiveFst_inr (M N : Module) :
    Hom.comp (additiveFst M N) (additiveInr M N) = 0 := by
  simp [additiveInr]

/-- Candidate inverse for pointwise-product reflexivity. -/
noncomputable def additiveProductDoubleDualInv
    {M N : Module}
    (hM : CanonicalReflexivity M) (hN : CanonicalReflexivity N) :
    Hom (DayNegation.neg (DayNegation.neg (additiveProduct M N)))
      (additiveProduct M N) :=
  additivePair
    (Hom.comp hM.inv
      (DayNegation.map (DayNegation.map (additiveFst M N))))
    (Hom.comp hN.inv
      (DayNegation.map (DayNegation.map (additiveSnd M N))))

/-- One triangle of product reflexivity: `inv ∘ unit = id`.

The reverse triangle `unit ∘ inv = id` (needed to package
`additiveProduct M N` as a `ClassicalObject`) is not proved here. -/
theorem additiveProduct_inv_hom
    {M N : Module}
    (hM : CanonicalReflexivity M) (hN : CanonicalReflexivity N) :
    Hom.comp (additiveProductDoubleDualInv hM hN)
      (DayNegation.unit (additiveProduct M N)) =
      Hom.id (additiveProduct M N) := by
  apply Hom.ext
  intro n x
  apply Prod.ext
  · change (hM.inv.app n
        ((DayNegation.map (DayNegation.map (additiveFst M N))).app n
          ((DayNegation.unit (additiveProduct M N)).app n x))) =
      x.1
    have hnat := congrArg (fun f : Hom _ _ => f.app n x)
      (DayNegation.unit_natural (additiveFst M N))
    change
      (DayNegation.unit M).app n ((additiveFst M N).app n x) =
        ((DayNegation.map (DayNegation.map (additiveFst M N))).app n
          ((DayNegation.unit (additiveProduct M N)).app n x)) at hnat
    exact (congrArg (hM.inv.app n) hnat.symm).trans
      (congrArg (fun f : Hom M M => f.app n x.1) hM.inv_hom)
  · change (hN.inv.app n
        ((DayNegation.map (DayNegation.map (additiveSnd M N))).app n
          ((DayNegation.unit (additiveProduct M N)).app n x))) =
      x.2
    have hnat := congrArg (fun f : Hom _ _ => f.app n x)
      (DayNegation.unit_natural (additiveSnd M N))
    change
      (DayNegation.unit N).app n ((additiveSnd M N).app n x) =
        ((DayNegation.map (DayNegation.map (additiveSnd M N))).app n
          ((DayNegation.unit (additiveProduct M N)).app n x)) at hnat
    exact (congrArg (hN.inv.app n) hnat.symm).trans
      (congrArg (fun f : Hom N N => f.app n x.2) hN.inv_hom)

/-! ## Classical bit as Yoneda biproduct `y(1+1) ≅ y(2)`

Per arXiv, `⟦Bit⟧ = I ⊕ I`.  In the CP-presheaf model the correct ⊕ for
finite-dimensional systems is the base-category biproduct preserved by
Yoneda: `y(1) ⊕ y(1) = y(1+1) = y(2)`.  The pointwise module product
`additiveProduct I I` is a different construction (categorical product of
modules) and is *not* isomorphic to `y(2)` under the TNI/effect-sum
constraint; it is retained above only as product scaffolding.
-/

open Matrix

/-- Isometry matrix `Fin 1 → Fin 2` placing mass at classical bit `b`. -/
def embedBitMatrix (b : Fin 2) : Matrix (Fin 2) (Fin 1) ℂ :=
  fun i _ => if i = b then 1 else 0

theorem embedBitMatrix_isometry (b : Fin 2) :
    (embedBitMatrix b)ᴴ * embedBitMatrix b = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [embedBitMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Superoperator embedding of the unit into the `b`-th basis ray of `y(2)`. -/
noncomputable def bitEmbedSO (b : Fin 2) : Superoperator 1 2 :=
  Superoperator.ofIsometry (embedBitMatrix b) (embedBitMatrix_isometry b)

/-- Postcomposition `y(A) → y(B)` induced by a fixed superoperator `A → B`. -/
noncomputable def representablePostcomp {A B : ℕ} (φ : Superoperator A B) :
    Hom (representable A) (representable B) where
  app := fun _ x => Superoperator.comp φ x
  map_zero := fun _ => Superoperator.comp_zero_right _
  map_sum := fun h => SigmaMon.ChoiSum.comp_left φ h
  naturality := by
    intro m n x f
    change Superoperator.comp φ (Superoperator.comp x f) =
      Superoperator.comp (Superoperator.comp φ x) f
    exact Superoperator.comp_assoc φ x f

/-- Yoneda bit carrier: `I ⊕ I = y(1+1)`. -/
noncomputable abbrev additiveBitModule : Module :=
  representable (1 + 1)

/-- `y(1+1) ≅ y(2)` (definitional on `ℕ`, packaged as a module `Iso`). -/
noncomputable def additiveBitIso :
    Iso additiveBitModule (representable 2) where
  hom := Hom.id _
  inv := Hom.id _
  hom_inv := Hom.id_comp _
  inv_hom := Hom.id_comp _

theorem additiveBitModule_eq_representable :
    additiveBitModule = representable 2 :=
  rfl

/-- Left classical bit injection `I → y(2)`. -/
noncomputable def bitInl : Hom dayTensorUnit (representable 2) :=
  representablePostcomp (bitEmbedSO 0)

/-- Right classical bit injection `I → y(2)`. -/
noncomputable def bitInr : Hom dayTensorUnit (representable 2) :=
  representablePostcomp (bitEmbedSO 1)

/-- Classical bit object: transport classicality of `y(2)` along `additiveBitIso`. -/
noncomputable def bitClassicalObject :
    ClassicalObject DayNegation.data :=
  ClassicalObject.ofIso
    (representableClassicalObject 2 (by decide))
    additiveBitIso.symm

theorem bitClassicalObject_module :
    bitClassicalObject.module = additiveBitModule :=
  rfl

end SuperoperatorModule

end QLambda.Domain.Presheaf
