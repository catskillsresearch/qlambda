/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.Presheaf.CPMap
import QLambda.Composer.MatrixSemantics

/-!
# Trace-nonincreasing intrinsic superoperators

The CP component is an intrinsic Choi matrix.  Trace non-increase is a
property of its action and therefore does not depend on a Kraus presentation.
-/

namespace QLambda.Domain.Presheaf

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

/-- Trace non-increase for an intrinsic CP map. -/
def TraceNonincreasing {n m : ℕ} (Φ : CPMap n m) : Prop :=
  ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
    (Matrix.trace (Φ.applyMat ρ)).re ≤ (Matrix.trace ρ).re

/-- Intrinsic trace non-increase is exactly the input-effect bound.  Notice
that this bounds the output partial trace of the Choi matrix, not the whole
Choi matrix itself. -/
theorem traceNonincreasing_iff_effect_le_one {n m : ℕ} (Φ : CPMap n m) :
    TraceNonincreasing Φ ↔ Φ.effect ≤ 1 :=
  ⟨CPMap.effect_le_one_of_trace_nonincreasing Φ,
    CPMap.trace_nonincreasing_of_effect_le_one Φ⟩

/-- A finite-dimensional trace-nonincreasing completely positive map. -/
structure Superoperator (n m : ℕ) where
  cp : CPMap n m
  trace_nonincreasing : TraceNonincreasing cp

namespace Superoperator

variable {n m ℓ r : ℕ}

@[ext]
theorem ext {Φ Ψ : Superoperator n m} (h : Φ.cp = Ψ.cp) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

/-- Build an intrinsic superoperator from a Kraus family and a proof about
its operator-sum action. -/
def ofKraus (K : KrausFamily n m)
    (hK : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef →
      (Matrix.trace (KrausFamily.applyMat K ρ)).re ≤
        (Matrix.trace ρ).re) :
    Superoperator n m where
  cp := CPMap.ofKraus K
  trace_nonincreasing := by
    intro ρ hρ
    simpa using hK ρ hρ

/-- Forget a finite Kraus presentation while preserving its TNI proof. -/
def ofQuantumOperation (Φ : QuantumOperation n m) : Superoperator n m :=
  ofKraus Φ.kraus Φ.trace_nonincreasing

@[simp]
theorem cp_ofQuantumOperation (Φ : QuantumOperation n m) :
    (ofQuantumOperation Φ).cp = CPMap.ofKraus Φ.kraus :=
  rfl

/-- Recover an arbitrary finite Kraus presentation. -/
noncomputable def toQuantumOperation (Φ : Superoperator n m) :
    QuantumOperation n m where
  kraus := Φ.cp.toKraus
  trace_nonincreasing := Φ.trace_nonincreasing

@[simp]
theorem ofQuantumOperation_toQuantumOperation (Φ : Superoperator n m) :
    ofQuantumOperation (toQuantumOperation Φ) = Φ := by
  apply ext
  exact CPMap.ofKraus_toKraus Φ.cp

@[simp]
theorem cp_toQuantumOperation (Φ : Superoperator n m) :
    CPMap.ofKraus (toQuantumOperation Φ).kraus = Φ.cp :=
  CPMap.ofKraus_toKraus Φ.cp

/-- Identity superoperator. -/
def identity (n : ℕ) : Superoperator n n where
  cp := CPMap.identity n
  trace_nonincreasing := by
    intro ρ _
    rw [CPMap.applyMat_identity]

/-- Zero superoperator. -/
def zero : Superoperator n m where
  cp := 0
  trace_nonincreasing := by
    intro ρ hρ
    have htr : 0 ≤ Matrix.trace ρ := PosSemidef.trace_nonneg hρ
    rw [CPMap.applyMat_zero, Matrix.trace_zero, Complex.zero_re]
    exact (RCLike.nonneg_iff (K := ℂ).mp htr).1

instance : Zero (Superoperator n m) := ⟨zero⟩

@[simp]
theorem cp_zero : (0 : Superoperator n m).cp = 0 :=
  rfl

@[simp]
theorem applyMat_zero (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (0 : Superoperator n m).cp.applyMat ρ = 0 :=
  CPMap.applyMat_zero ρ

/-- Every CP map below a TNI map in Choi order is itself TNI. -/
noncomputable def ofLE (Φ : CPMap n m) (Ψ : Superoperator n m)
    (h : Φ ≤ Ψ.cp) : Superoperator n m where
  cp := Φ
  trace_nonincreasing := by
    intro ρ hρ
    let R : CPMap n m := CPMap.residualOfLE h
    have hsum : Φ + R = Ψ.cp := CPMap.add_residualOfLE h
    have hRtrace :
        0 ≤ (Matrix.trace (R.applyMat ρ)).re := by
      have hpos := CPMap.applyMat_posSemidef R hρ
      exact
        (RCLike.nonneg_iff (K := ℂ).mp
          (Matrix.PosSemidef.trace_nonneg hpos)).1
    have htni := Ψ.trace_nonincreasing ρ hρ
    rw [← hsum, CPMap.applyMat_add_map, Matrix.trace_add,
      Complex.add_re] at htni
    linarith

@[simp]
theorem cp_ofLE (Φ : CPMap n m) (Ψ : Superoperator n m)
    (h : Φ ≤ Ψ.cp) :
    (ofLE Φ Ψ h).cp = Φ :=
  rfl

/-- Sequential composition, first `Φ` and then `Ψ`. -/
noncomputable def comp (Ψ : Superoperator m ℓ) (Φ : Superoperator n m) :
    Superoperator n ℓ where
  cp := CPMap.comp Ψ.cp Φ.cp
  trace_nonincreasing := by
    intro ρ hρ
    rw [CPMap.applyMat_comp]
    exact
      (Ψ.trace_nonincreasing _ (CPMap.applyMat_posSemidef Φ.cp hρ)).trans
        (Φ.trace_nonincreasing ρ hρ)

@[simp]
theorem cp_comp (Ψ : Superoperator m ℓ) (Φ : Superoperator n m) :
    (comp Ψ Φ).cp = CPMap.comp Ψ.cp Φ.cp :=
  rfl

@[simp]
theorem identity_comp (Φ : Superoperator n m) :
    comp (identity m) Φ = Φ :=
  ext (CPMap.identity_comp Φ.cp)

@[simp]
theorem comp_identity (Φ : Superoperator n m) :
    comp Φ (identity n) = Φ :=
  ext (CPMap.comp_identity Φ.cp)

theorem comp_assoc (Χ : Superoperator ℓ r) (Ψ : Superoperator m ℓ)
    (Φ : Superoperator n m) :
    comp Χ (comp Ψ Φ) = comp (comp Χ Ψ) Φ :=
  ext (CPMap.comp_assoc Χ.cp Ψ.cp Φ.cp)

@[simp]
theorem comp_zero_left (Φ : Superoperator n m) :
    comp (0 : Superoperator m ℓ) Φ = 0 :=
  ext (CPMap.comp_zero_left Φ.cp)

@[simp]
theorem comp_zero_right (Ψ : Superoperator m ℓ) :
    comp Ψ (0 : Superoperator n m) = 0 :=
  ext (CPMap.comp_zero_right Ψ.cp)

/-- Parallel composition of finite-dimensional superoperators.  Trace
non-increase is proved through the intrinsic effect bound, hence applies to
arbitrary positive (in particular, entangled) joint inputs. -/
def tensor (Φ : Superoperator n m) (Ψ : Superoperator ℓ r) :
    Superoperator (n * ℓ) (m * r) where
  cp := CPMap.tensor Φ.cp Ψ.cp
  trace_nonincreasing :=
    CPMap.trace_nonincreasing_tensor Φ.cp Ψ.cp
      Φ.trace_nonincreasing Ψ.trace_nonincreasing

@[simp]
theorem cp_tensor (Φ : Superoperator n m) (Ψ : Superoperator ℓ r) :
    (tensor Φ Ψ).cp = CPMap.tensor Φ.cp Ψ.cp :=
  rfl

@[simp]
theorem tensor_zero_left (Ψ : Superoperator ℓ r) :
    tensor (0 : Superoperator n m) Ψ = 0 :=
  ext (CPMap.tensor_zero_left Ψ.cp)

@[simp]
theorem tensor_zero_right (Φ : Superoperator n m) :
    tensor Φ (0 : Superoperator ℓ r) = 0 :=
  ext (CPMap.tensor_zero_right Φ.cp)

/-- Parallel composition is a bifunctor: it preserves sequential
composition in both arguments. -/
theorem tensor_comp {p q : ℕ}
    (Φ₂ : Superoperator m p) (Φ₁ : Superoperator n m)
    (Ψ₂ : Superoperator r q) (Ψ₁ : Superoperator ℓ r) :
    tensor (comp Φ₂ Φ₁) (comp Ψ₂ Ψ₁) =
      comp (tensor Φ₂ Ψ₂) (tensor Φ₁ Ψ₁) :=
  ext (CPMap.tensor_comp Φ₂.cp Φ₁.cp Ψ₂.cp Ψ₁.cp)

/-- Parallel composition preserves identity maps. -/
@[simp]
theorem tensor_identity (n ℓ : ℕ) :
    tensor (identity n) (identity ℓ) = identity (n * ℓ) :=
  ext (CPMap.tensor_identity n ℓ)

/-- Action on a sub-normalized density operator. -/
noncomputable def apply (Φ : Superoperator n m) (ρ : SubNormalizedDensity n) :
    SubNormalizedDensity m where
  mat := Φ.cp.applyMat ρ.mat
  posSemidef := CPMap.applyMat_posSemidef Φ.cp ρ.posSemidef
  trace_le_one :=
    (Φ.trace_nonincreasing ρ.mat ρ.posSemidef).trans ρ.trace_le_one

@[simp]
theorem apply_mat (Φ : Superoperator n m) (ρ : SubNormalizedDensity n) :
    (apply Φ ρ).mat = Φ.cp.applyMat ρ.mat :=
  rfl

/-- A one-Kraus isometry, covering physical embeddings and unitary maps. -/
def ofIsometry (A : KrausOperator n m) (hA : Aᴴ * A = 1) :
    Superoperator n m :=
  ofQuantumOperation (QuantumOperation.ofIsometry A hA)

/-- A square isometry, named for its usual physical use. -/
def unitary (U : KrausOperator n n) (hU : Uᴴ * U = 1) :
    Superoperator n n :=
  ofIsometry U hU

@[simp]
theorem cp_ofIsometry (A : KrausOperator n m) (hA : Aᴴ * A = 1) :
    (ofIsometry A hA).cp = CPMap.ofKraus [A] :=
  rfl

/-- The permutation matrix associated to an equivalence of finite bases. -/
def equivalenceMatrix {n m : ℕ} (e : Fin n ≃ Fin m) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun i j => if i = e j then 1 else 0

theorem equivalenceMatrix_isometry {n m : ℕ} (e : Fin n ≃ Fin m) :
    (equivalenceMatrix e)ᴴ * equivalenceMatrix e = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, equivalenceMatrix]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem equivalenceMatrix_comp {n m ℓ : ℕ}
    (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin ℓ) :
    equivalenceMatrix (e.trans f) =
      equivalenceMatrix f * equivalenceMatrix e := by
  ext i j
  simp [equivalenceMatrix, Matrix.mul_apply]
  rfl

/-- A finite basis equivalence as a reversible superoperator. -/
def ofEquivalence {n m : ℕ} (e : Fin n ≃ Fin m) :
    Superoperator n m :=
  ofIsometry (equivalenceMatrix e) (equivalenceMatrix_isometry e)

@[simp]
theorem ofEquivalence_comp {n m ℓ : ℕ}
    (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin ℓ) :
    comp (ofEquivalence f) (ofEquivalence e) =
      ofEquivalence (e.trans f) := by
  apply ext
  apply CPMap.ext_apply
  intro ρ
  simp only [cp_comp, CPMap.applyMat_comp]
  simp only [ofEquivalence, ofIsometry, ofQuantumOperation, ofKraus,
    CPMap.applyMat_ofKraus, KrausFamily.applyMat,
    QuantumOperation.ofIsometry]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rw [equivalenceMatrix_comp, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

@[simp]
theorem ofEquivalence_refl (n : ℕ) :
    ofEquivalence (Equiv.refl (Fin n)) = identity n := by
  apply ext
  apply CPMap.ext_apply
  intro ρ
  simp only [ofEquivalence, identity, CPMap.identity, ofIsometry,
    ofQuantumOperation, ofKraus, CPMap.applyMat_ofKraus,
    KrausFamily.applyMat, QuantumOperation.ofIsometry,
    KrausFamily.identity]
  have h : equivalenceMatrix (Equiv.refl (Fin n)) = 1 := by
    ext i j
    simp [equivalenceMatrix, Matrix.one_apply]
    rfl
  rw [h]

theorem comp_ofEquivalence_finCongr {n a b : ℕ} (h : a = b)
    (x : Superoperator n a) :
    comp (ofEquivalence (finCongr h)) x = h ▸ x := by
  subst b
  simp

/-- The canonical reassociation of three finite tensor-product bases. -/
def tensorAssociatorEquiv (a b c : ℕ) :
    Fin ((a * b) * c) ≃ Fin (a * (b * c)) :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl (Fin c))).trans
      ((Equiv.prodAssoc (Fin a) (Fin b) (Fin c)).trans
        ((Equiv.prodCongr (Equiv.refl (Fin a)) finProdFinEquiv).trans
          finProdFinEquiv)))

/-- The canonical left-unitor equivalence of finite tensor-product bases. -/
def tensorLeftUnitorEquiv (a : ℕ) : Fin (1 * a) ≃ Fin a :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodCongr finOneEquiv (Equiv.refl (Fin a))).trans
      (Equiv.punitProd (Fin a)))

/-- The canonical right-unitor equivalence of finite tensor-product bases. -/
def tensorRightUnitorEquiv (a : ℕ) : Fin (a * 1) ≃ Fin a :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodCongr (Equiv.refl (Fin a)) finOneEquiv).trans
      (Equiv.prodPUnit (Fin a)))

/-- The canonical swap of two finite tensor-product bases. -/
def tensorSwapEquiv (a b : ℕ) : Fin (a * b) ≃ Fin (b * a) :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodComm (Fin a) (Fin b)).trans finProdFinEquiv)

/-- Tensor product of finite basis equivalences. -/
def tensorEquiv {a a' b b' : ℕ}
    (e : Fin a ≃ Fin a') (f : Fin b ≃ Fin b') :
    Fin (a * b) ≃ Fin (a' * b') :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodCongr e f).trans finProdFinEquiv)

theorem choi_ofEquivalence_apply {n m : ℕ} (e : Fin n ≃ Fin m)
    (a b : Fin m) (i j : Fin n) :
    (ofEquivalence e).cp.choi (a, i) (b, j) =
      (if a = e i ∧ b = e j then 1 else 0) := by
  simp only [ofEquivalence, ofIsometry, ofQuantumOperation, ofKraus,
    CPMap.choi_ofKraus, QuantumOperation.ofIsometry,
    KrausFamily.choi_single, KrausFamily.choiTerm, equivalenceMatrix]
  by_cases hai : a = e i <;> by_cases hbj : b = e j <;>
    simp [hai, hbj]

theorem choi_comp_ofEquivalence_right {n m ℓ : ℕ}
    (e : Fin n ≃ Fin m) (Φ : Superoperator m ℓ)
    (a b : Fin ℓ) (i j : Fin n) :
    (comp Φ (ofEquivalence e)).cp.choi (a, i) (b, j) =
      Φ.cp.choi (a, e i) (b, e j) := by
  classical
  rw [cp_comp, CPMap.choi_comp_apply]
  simp only [choi_ofEquivalence_apply]
  rw [Finset.sum_eq_single (e i)]
  · rw [Finset.sum_eq_single (e j)]
    · simp
    · intro y _ hy
      simp [hy]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intro x _ hx
    simp [hx]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem choi_comp_ofEquivalence_left {n m ℓ : ℕ}
    (e : Fin m ≃ Fin ℓ) (Φ : Superoperator n m)
    (a b : Fin ℓ) (i j : Fin n) :
    (comp (ofEquivalence e) Φ).cp.choi (a, i) (b, j) =
      Φ.cp.choi (e.symm a, i) (e.symm b, j) := by
  classical
  rw [cp_comp, CPMap.choi_comp_apply]
  simp only [choi_ofEquivalence_apply]
  rw [Finset.sum_eq_single (e.symm a)]
  · rw [Finset.sum_eq_single (e.symm b)]
    · simp
    · intro y _ hy
      have hne : b ≠ e y := by
        intro h
        apply hy
        apply e.injective
        simpa using h.symm
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intro x _ hx
    have hne : a ≠ e x := by
      intro h
      apply hx
      apply e.injective
      simpa using h.symm
    simp [hne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Left composition with a basis equivalence preserves the input effect
(unitary postprocessing does not change the Heisenberg effect). -/
theorem effect_comp_ofEquivalence_left {n m ℓ : ℕ}
    (e : Fin m ≃ Fin ℓ) (Φ : Superoperator n m) :
    (comp (ofEquivalence e) Φ).cp.effect = Φ.cp.effect := by
  ext i j
  simp only [CPMap.effect]
  have hterm (a : Fin ℓ) :
      (comp (ofEquivalence e) Φ).cp.choi (a, j) (a, i) =
        Φ.cp.choi (e.symm a, j) (e.symm a, i) :=
    choi_comp_ofEquivalence_left e Φ a a j i
  simp_rw [hterm]
  exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

@[simp]
theorem tensor_ofEquivalence {a a' b b' : ℕ}
    (e : Fin a ≃ Fin a') (f : Fin b ≃ Fin b') :
    tensor (ofEquivalence e) (ofEquivalence f) =
      ofEquivalence (tensorEquiv e f) := by
  apply ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨x, i⟩
  rcases bj with ⟨y, j⟩
  simp only [cp_tensor, CPMap.choi_tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    choi_ofEquivalence_apply]
  dsimp [CPMap.choiTensorEquiv, tensorEquiv]
  rw [choi_ofEquivalence_apply, choi_ofEquivalence_apply]
  have hx :
      x = finProdFinEquiv (e i.divNat, f i.modNat) ↔
        x.divNat = e i.divNat ∧ x.modNat = f i.modNat := by
    constructor
    · intro h
      subst x
      have h := finProdFinEquiv.left_inv (e i.divNat, f i.modNat)
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨h₁, h₂⟩
      rw [← finProdFinEquiv.apply_symm_apply x]
      exact congrArg finProdFinEquiv (Prod.ext h₁ h₂)
  have hy :
      y = finProdFinEquiv (e j.divNat, f j.modNat) ↔
        y.divNat = e j.divNat ∧ y.modNat = f j.modNat := by
    constructor
    · intro h
      subst y
      have h := finProdFinEquiv.left_inv (e j.divNat, f j.modNat)
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨h₁, h₂⟩
      rw [← finProdFinEquiv.apply_symm_apply y]
      exact congrArg finProdFinEquiv (Prod.ext h₁ h₂)
  split <;> split <;> simp_all

/-- Reversible superoperator implementing tensor reassociation. -/
def tensorAssociator (a b c : ℕ) :
    Superoperator ((a * b) * c) (a * (b * c)) :=
  ofEquivalence (tensorAssociatorEquiv a b c)

/-- Reversible superoperator implementing the left tensor unitor. -/
def tensorLeftUnitor (a : ℕ) : Superoperator (1 * a) a :=
  ofEquivalence (tensorLeftUnitorEquiv a)

/-- Reversible superoperator implementing the right tensor unitor. -/
def tensorRightUnitor (a : ℕ) : Superoperator (a * 1) a :=
  ofEquivalence (tensorRightUnitorEquiv a)

/-- Reversible superoperator implementing tensor-factor swap. -/
def tensorSwap (a b : ℕ) : Superoperator (a * b) (b * a) :=
  ofEquivalence (tensorSwapEquiv a b)

def tensorAssociatorInv (a b c : ℕ) :
    Superoperator (a * (b * c)) ((a * b) * c) :=
  ofEquivalence (tensorAssociatorEquiv a b c).symm

def tensorLeftUnitorInv (a : ℕ) : Superoperator a (1 * a) :=
  ofEquivalence (tensorLeftUnitorEquiv a).symm

def tensorRightUnitorInv (a : ℕ) : Superoperator a (a * 1) :=
  ofEquivalence (tensorRightUnitorEquiv a).symm

@[simp]
theorem tensorAssociator_hom_inv (a b c : ℕ) :
    comp (tensorAssociator a b c) (tensorAssociatorInv a b c) =
      identity (a * (b * c)) := by
  rw [tensorAssociator, tensorAssociatorInv, ofEquivalence_comp]
  convert ofEquivalence_refl (a * (b * c))
  ext
  simp

@[simp]
theorem tensorAssociator_inv_hom (a b c : ℕ) :
    comp (tensorAssociatorInv a b c) (tensorAssociator a b c) =
      identity ((a * b) * c) := by
  rw [tensorAssociator, tensorAssociatorInv, ofEquivalence_comp]
  convert ofEquivalence_refl ((a * b) * c)
  ext
  simp

@[simp]
theorem tensorLeftUnitor_hom_inv (a : ℕ) :
    comp (tensorLeftUnitor a) (tensorLeftUnitorInv a) = identity a := by
  rw [tensorLeftUnitor, tensorLeftUnitorInv, ofEquivalence_comp]
  convert ofEquivalence_refl a
  ext
  simp

@[simp]
theorem tensorLeftUnitor_inv_hom (a : ℕ) :
    comp (tensorLeftUnitorInv a) (tensorLeftUnitor a) =
      identity (1 * a) := by
  rw [tensorLeftUnitor, tensorLeftUnitorInv, ofEquivalence_comp]
  convert ofEquivalence_refl (1 * a)
  ext
  simp

@[simp]
theorem tensorRightUnitor_hom_inv (a : ℕ) :
    comp (tensorRightUnitor a) (tensorRightUnitorInv a) = identity a := by
  rw [tensorRightUnitor, tensorRightUnitorInv, ofEquivalence_comp]
  convert ofEquivalence_refl a
  ext
  simp

@[simp]
theorem tensorRightUnitor_inv_hom (a : ℕ) :
    comp (tensorRightUnitorInv a) (tensorRightUnitor a) =
      identity (a * 1) := by
  rw [tensorRightUnitor, tensorRightUnitorInv, ofEquivalence_comp]
  convert ofEquivalence_refl (a * 1)
  ext
  simp

@[simp]
theorem tensorSwap_involutive (a b : ℕ) :
    comp (tensorSwap b a) (tensorSwap a b) = identity (a * b) := by
  rw [tensorSwap, tensorSwap, ofEquivalence_comp]
  convert ofEquivalence_refl (a * b)
  ext x
  simp [tensorSwapEquiv]
  exact Nat.mod_add_div x.val b

theorem tensor_pentagon (a b c d : ℕ) :
    comp (tensorAssociator a b (c * d))
        (tensorAssociator (a * b) c d) =
      comp (tensor (identity a) (tensorAssociator b c d))
        (comp (tensorAssociator a (b * c) d)
          (tensor (tensorAssociator a b c) (identity d))) := by
  rw [← ofEquivalence_refl a, ← ofEquivalence_refl d]
  simp only [tensorAssociator, tensor_ofEquivalence, tensorEquiv,
    ofEquivalence_comp]
  congr 1
  ext x
  simp [tensorAssociatorEquiv]

theorem tensor_triangle (a b : ℕ) :
    comp (tensor (identity a) (tensorLeftUnitor b))
        (tensorAssociator a 1 b) =
      tensor (tensorRightUnitor a) (identity b) := by
  simp only [tensorAssociator, tensorLeftUnitor, tensorRightUnitor,
    ← ofEquivalence_refl, tensor_ofEquivalence, ofEquivalence_comp]
  congr 1
  ext x
  simp [tensorAssociatorEquiv, tensorLeftUnitorEquiv,
    tensorRightUnitorEquiv, tensorEquiv]

/-- Right-unitor / associator coherence on finite tensor bases:
`(id ⊗ ρ) ∘ α = ρ`. -/
theorem tensor_rightUnitor_associator (a b : ℕ) :
    comp (tensor (identity a) (tensorRightUnitor b))
        (tensorAssociator a b 1) =
      tensorRightUnitor (a * b) := by
  simp only [tensorAssociator, tensorRightUnitor,
    ← ofEquivalence_refl, tensor_ofEquivalence, ofEquivalence_comp]
  congr 1
  ext x
  simp [tensorAssociatorEquiv, tensorRightUnitorEquiv, tensorEquiv]
  rw [Nat.mul_comm b]
  exact Nat.mod_add_div' (↑x) b

theorem tensor_hexagon (a b c : ℕ) :
    comp (tensorSwap a (b * c)) (tensorAssociator a b c) =
      comp (tensorAssociatorInv b c a)
        (comp (tensor (identity b) (tensorSwap a c))
          (comp (tensorAssociator b a c)
            (tensor (tensorSwap a b) (identity c)))) := by
  simp only [tensorAssociator, tensorAssociatorInv, tensorSwap,
    ← ofEquivalence_refl, tensor_ofEquivalence, ofEquivalence_comp]
  congr 1
  ext x
  simp [tensorAssociatorEquiv, tensorSwapEquiv, tensorEquiv]

/-- Reassociation in the reverse direction, expressed using only forward
associators and symmetric braidings. -/
theorem tensorAssociatorInv_braiding (a b c : ℕ) :
    comp (tensorSwap c (a * b))
      (comp (tensorAssociator c a b)
        (comp (tensorSwap b (c * a))
          (comp (tensorAssociator b c a)
            (tensorSwap a (b * c))))) =
      tensorAssociatorInv a b c := by
  simp only [tensorAssociator, tensorAssociatorInv, tensorSwap,
    ofEquivalence_comp]
  congr 1
  ext x
  simp [tensorAssociatorEquiv, tensorSwapEquiv]

theorem tensorAssociator_naturality
    {a a' b b' c c' : ℕ}
    (f : Superoperator a a') (g : Superoperator b b')
    (h : Superoperator c c') :
    comp (tensorAssociator a' b' c') (tensor (tensor f g) h) =
      comp (tensor f (tensor g h)) (tensorAssociator a b c) := by
  apply ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨x, i⟩
  rcases bj with ⟨y, j⟩
  rw [show tensorAssociator a' b' c' =
    ofEquivalence (tensorAssociatorEquiv a' b' c') from rfl,
    choi_comp_ofEquivalence_left]
  rw [show tensorAssociator a b c =
    ofEquivalence (tensorAssociatorEquiv a b c) from rfl,
    choi_comp_ofEquivalence_right]
  simp only [cp_tensor, CPMap.choi_tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  dsimp [CPMap.choiTensorEquiv, tensorAssociatorEquiv]
  simp
  ring

/-- Natural form of `tensor_rightUnitor_associator` with a unit wire. -/
theorem tensor_rightUnitor_associator_naturality {u : ℕ}
    (a b : ℕ) (q : Superoperator u 1) :
    comp
        (tensor (identity a)
          (comp (tensorRightUnitor b)
            (tensor (identity b) q)))
        (tensorAssociator a b u) =
      comp (tensorRightUnitor (a * b))
        (tensor (identity (a * b)) q) := by
  calc
    comp
        (tensor (identity a)
          (comp (tensorRightUnitor b)
            (tensor (identity b) q)))
        (tensorAssociator a b u) =
      comp (tensor (identity a) (tensorRightUnitor b))
        (comp (tensor (identity a) (tensor (identity b) q))
          (tensorAssociator a b u)) := by
            rw [comp_assoc, ← tensor_comp]; simp
    _ = comp (tensor (identity a) (tensorRightUnitor b))
        (comp (tensorAssociator a b 1)
          (tensor (tensor (identity a) (identity b)) q)) := by
            rw [← tensorAssociator_naturality]
    _ = comp
        (comp (tensor (identity a) (tensorRightUnitor b))
          (tensorAssociator a b 1))
        (tensor (tensor (identity a) (identity b)) q) := by
            rw [comp_assoc]
    _ = comp (tensorRightUnitor (a * b))
        (tensor (tensor (identity a) (identity b)) q) := by
            rw [tensor_rightUnitor_associator]
    _ = comp (tensorRightUnitor (a * b))
        (tensor (identity (a * b)) q) := by
            rw [tensor_identity]

theorem tensorLeftUnitor_naturality {a a' : ℕ}
    (f : Superoperator a a') :
    comp (tensorLeftUnitor a') (tensor (identity 1) f) =
      comp f (tensorLeftUnitor a) := by
  apply ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨x, i⟩
  rcases bj with ⟨y, j⟩
  rw [show tensorLeftUnitor a' =
    ofEquivalence (tensorLeftUnitorEquiv a') from rfl,
    choi_comp_ofEquivalence_left]
  rw [show tensorLeftUnitor a =
    ofEquivalence (tensorLeftUnitorEquiv a) from rfl,
    choi_comp_ofEquivalence_right]
  simp only [cp_tensor, CPMap.choi_tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  dsimp [CPMap.choiTensorEquiv, tensorLeftUnitorEquiv, identity,
    CPMap.identity, KrausFamily.identity, KrausFamily.choi,
    KrausFamily.choiTerm]
  have hi : finOneEquiv.symm PUnit.unit = i.divNat :=
    Subsingleton.elim _ _
  have hj : finOneEquiv.symm PUnit.unit = j.divNat :=
    Subsingleton.elim _ _
  have hij : i.divNat = j.divNat := Subsingleton.elim _ _
  simp [KrausFamily.choiTerm, hi, hij]

theorem tensorRightUnitor_naturality {a a' : ℕ}
    (f : Superoperator a a') :
    comp (tensorRightUnitor a') (tensor f (identity 1)) =
      comp f (tensorRightUnitor a) := by
  apply ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨x, i⟩
  rcases bj with ⟨y, j⟩
  rw [show tensorRightUnitor a' =
    ofEquivalence (tensorRightUnitorEquiv a') from rfl,
    choi_comp_ofEquivalence_left]
  rw [show tensorRightUnitor a =
    ofEquivalence (tensorRightUnitorEquiv a) from rfl,
    choi_comp_ofEquivalence_right]
  simp only [cp_tensor, CPMap.choi_tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  dsimp [CPMap.choiTensorEquiv, tensorRightUnitorEquiv, identity,
    CPMap.identity, KrausFamily.identity, KrausFamily.choi,
    KrausFamily.choiTerm]
  have hi : finOneEquiv.symm PUnit.unit = i.modNat :=
    Subsingleton.elim _ _
  have hj : finOneEquiv.symm PUnit.unit = j.modNat :=
    Subsingleton.elim _ _
  have hij : i.modNat = j.modNat := Subsingleton.elim _ _
  simp [KrausFamily.choiTerm, hi, hij]

theorem tensorSwap_naturality {a a' b b' : ℕ}
    (f : Superoperator a a') (g : Superoperator b b') :
    comp (tensorSwap a' b') (tensor f g) =
      comp (tensor g f) (tensorSwap a b) := by
  apply ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨x, i⟩
  rcases bj with ⟨y, j⟩
  rw [show tensorSwap a' b' =
    ofEquivalence (tensorSwapEquiv a' b') from rfl,
    choi_comp_ofEquivalence_left]
  rw [show tensorSwap a b =
    ofEquivalence (tensorSwapEquiv a b) from rfl,
    choi_comp_ofEquivalence_right]
  simp only [cp_tensor, CPMap.choi_tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  dsimp [CPMap.choiTensorEquiv, tensorSwapEquiv]
  simp
  ring

theorem tensorAssociatorInv_naturality
    {a a' b b' c c' : ℕ}
    (f : Superoperator a a') (g : Superoperator b b')
    (h : Superoperator c c') :
    comp (tensor (tensor f g) h) (tensorAssociatorInv a b c) =
      comp (tensorAssociatorInv a' b' c')
        (tensor f (tensor g h)) := by
  apply ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨x, i⟩
  rcases bj with ⟨y, j⟩
  rw [show tensorAssociatorInv a b c =
    ofEquivalence (tensorAssociatorEquiv a b c).symm from rfl,
    choi_comp_ofEquivalence_right]
  rw [show tensorAssociatorInv a' b' c' =
    ofEquivalence (tensorAssociatorEquiv a' b' c').symm from rfl,
    choi_comp_ofEquivalence_left]
  simp only [cp_tensor, CPMap.choi_tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  dsimp [CPMap.choiTensorEquiv, tensorAssociatorEquiv]
  simp
  ring

theorem tensorLeftUnitorInv_naturality {a a' : ℕ}
    (f : Superoperator a a') :
    comp (tensor (identity 1) f) (tensorLeftUnitorInv a) =
      comp (tensorLeftUnitorInv a') f := by
  apply ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨x, i⟩
  rcases bj with ⟨y, j⟩
  rw [show tensorLeftUnitorInv a =
    ofEquivalence (tensorLeftUnitorEquiv a).symm from rfl,
    choi_comp_ofEquivalence_right]
  rw [show tensorLeftUnitorInv a' =
    ofEquivalence (tensorLeftUnitorEquiv a').symm from rfl,
    choi_comp_ofEquivalence_left]
  simp only [cp_tensor, CPMap.choi_tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  dsimp [CPMap.choiTensorEquiv, tensorLeftUnitorEquiv, identity,
    CPMap.identity, KrausFamily.identity, KrausFamily.choi,
    KrausFamily.choiTerm]
  have hxy : x.divNat = y.divNat := Subsingleton.elim _ _
  have hone : y.divNat = finOneEquiv.symm PUnit.unit :=
    Subsingleton.elim _ _
  simp [KrausFamily.choiTerm, hxy, hone]

theorem tensorRightUnitorInv_naturality {a a' : ℕ}
    (f : Superoperator a a') :
    comp (tensor f (identity 1)) (tensorRightUnitorInv a) =
      comp (tensorRightUnitorInv a') f := by
  apply ext
  apply CPMap.ext
  ext ai bj
  rcases ai with ⟨x, i⟩
  rcases bj with ⟨y, j⟩
  rw [show tensorRightUnitorInv a =
    ofEquivalence (tensorRightUnitorEquiv a).symm from rfl,
    choi_comp_ofEquivalence_right]
  rw [show tensorRightUnitorInv a' =
    ofEquivalence (tensorRightUnitorEquiv a').symm from rfl,
    choi_comp_ofEquivalence_left]
  simp only [cp_tensor, CPMap.choi_tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  dsimp [CPMap.choiTensorEquiv, tensorRightUnitorEquiv, identity,
    CPMap.identity, KrausFamily.identity, KrausFamily.choi,
    KrausFamily.choiTerm]
  have hxy : x.modNat = y.modNat := Subsingleton.elim _ _
  have hone : y.modNat = finOneEquiv.symm PUnit.unit :=
    Subsingleton.elim _ _
  simp [KrausFamily.choiTerm, hxy, hone]

theorem tensor_triangle_naturality {u : ℕ}
    (a b : ℕ) (q : Superoperator u 1) :
    comp
        (tensor (identity a)
          (comp (tensorLeftUnitor b)
            (tensor q (identity b))))
        (tensorAssociator a u b) =
      tensor
        (comp (tensorRightUnitor a)
          (tensor (identity a) q))
        (identity b) := by
  calc
    comp
        (tensor (identity a)
          (comp (tensorLeftUnitor b)
            (tensor q (identity b))))
        (tensorAssociator a u b) =
      comp (tensor (identity a) (tensorLeftUnitor b))
        (comp (tensor (identity a)
          (tensor q (identity b)))
          (tensorAssociator a u b)) := by
            rw [comp_assoc, ← tensor_comp]
            simp
    _ = comp (tensor (identity a) (tensorLeftUnitor b))
        (comp (tensorAssociator a 1 b)
          (tensor (tensor (identity a) q) (identity b))) := by
            rw [← tensorAssociator_naturality]
    _ = comp
        (comp (tensor (identity a) (tensorLeftUnitor b))
          (tensorAssociator a 1 b))
        (tensor (tensor (identity a) q) (identity b)) := by
            rw [comp_assoc]
    _ = comp (tensor (tensorRightUnitor a) (identity b))
        (tensor (tensor (identity a) q) (identity b)) := by
            rw [tensor_triangle]
    _ = tensor
        (comp (tensorRightUnitor a)
          (tensor (identity a) q))
        (identity b) := by
            rw [← tensor_comp]
            simp

theorem allocZeroMatrix_isometry (q : ℕ) :
    (CompletedCP.allocZeroMatrix q)ᴴ * CompletedCP.allocZeroMatrix q = 1 := by
  ext i j
  have hdim : CQ.QDim q ≤ CQ.QDim (q + 1) := by
    change 2 ^ q ≤ 2 ^ (q + 1)
    rw [pow_succ]
    omega
  have hi (k : Fin (CQ.QDim (q + 1))) :
      k.val = i.val ↔ k = Fin.castLE hdim i := by
    constructor
    · intro h
      apply Fin.ext
      exact h
    · intro h
      exact congrArg Fin.val h
  have hj (k : Fin (CQ.QDim (q + 1))) :
      k.val = j.val ↔ k = Fin.castLE hdim j := by
    constructor
    · intro h
      apply Fin.ext
      exact h
    · intro h
      exact congrArg Fin.val h
  simp only [CompletedCP.allocZeroMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [hi, hj]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

/-- Allocate one fresh qubit in state `|0⟩`. -/
noncomputable def allocateZero (q : ℕ) :
    Superoperator (CQ.QDim q) (CQ.QDim (q + 1)) :=
  ofIsometry (CompletedCP.allocZeroMatrix q) (allocZeroMatrix_isometry q)

@[simp]
theorem cp_allocateZero (q : ℕ) :
    (allocateZero q).cp =
      CPMap.ofKraus [CompletedCP.allocZeroMatrix q] :=
  rfl

noncomputable def x {q : ℕ} (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.xMatrix w) (Composer.xMatrix_isometry w)

noncomputable def h {q : ℕ} (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.hMatrix w) (Composer.hMatrix_isometry w)

noncomputable def t {q : ℕ} (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.tMatrix w) (Composer.tMatrix_isometry w)

noncomputable def ry {q : ℕ} (θ : ℝ) (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.ryMatrix θ w) (Composer.ryMatrix_isometry θ w)

noncomputable def cx {q : ℕ} (control target : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  unitary (Composer.cxMatrix control target)
    (Composer.cxMatrix_isometry control target)

/-- Reset a retained wire to `|0⟩`, agreeing definitionally with the existing
two-Kraus operation. -/
noncomputable def reset {q : ℕ} (w : Fin q) :
    Superoperator (CQ.QDim q) (CQ.QDim q) :=
  ofQuantumOperation (Composer.reset w)

@[simp]
theorem cp_reset {q : ℕ} (w : Fin q) :
    (reset w).cp =
      CPMap.ofKraus [Composer.resetKraus w false, Composer.resetKraus w true] :=
  rfl

end Superoperator

end QLambda.Domain.Presheaf
