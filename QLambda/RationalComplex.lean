/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat

/-!
# Gaussian-rational test vectors

Choi matrices live over `ℂ`, but finite observations only need vectors
with rational real and imaginary parts.  These form a countable dense
subfield and therefore give a countable family of quadratic tests in
each fixed finite dimension.
-/

namespace QLambda

/-- A Gaussian rational, represented without quotienting or
normalization overhead. -/
@[ext]
structure RatComplex where
  re : ℚ
  im : ℚ
deriving DecidableEq

namespace RatComplex

/-- The Gaussian-rational imaginary unit. -/
def I : RatComplex := ⟨0, 1⟩

def equivProd : RatComplex ≃ ℚ × ℚ where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Encodable RatComplex :=
  Encodable.ofEquiv (ℚ × ℚ) equivProd

instance : Zero RatComplex := ⟨⟨0, 0⟩⟩
instance : One RatComplex := ⟨⟨1, 0⟩⟩
instance : Add RatComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg RatComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub RatComplex := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul RatComplex :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Star RatComplex := ⟨fun z => ⟨z.re, -z.im⟩⟩

@[simp] theorem zero_re : (0 : RatComplex).re = 0 := rfl
@[simp] theorem zero_im : (0 : RatComplex).im = 0 := rfl
@[simp] theorem one_re : (1 : RatComplex).re = 1 := rfl
@[simp] theorem one_im : (1 : RatComplex).im = 0 := rfl
@[simp] theorem add_re (z w : RatComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : RatComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : RatComplex) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : RatComplex) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : RatComplex) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : RatComplex) : (z - w).im = z.im - w.im := rfl
@[simp] theorem mul_re (z w : RatComplex) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : RatComplex) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem star_re (z : RatComplex) : (star z).re = z.re := rfl
@[simp] theorem star_im (z : RatComplex) : (star z).im = -z.im := rfl

/-- The canonical embedding of Gaussian rationals into the complex
numbers. -/
def toComplex (z : RatComplex) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * Complex.I

instance : Coe RatComplex ℂ := ⟨toComplex⟩

@[simp] theorem toComplex_re (z : RatComplex) :
    ((z : ℂ).re) = z.re := by
  simp [toComplex]

@[simp] theorem toComplex_im (z : RatComplex) :
    ((z : ℂ).im) = z.im := by
  simp [toComplex]

@[simp] theorem toComplex_zero : ((0 : RatComplex) : ℂ) = 0 := by
  apply Complex.ext <;> simp [toComplex]

@[simp] theorem toComplex_one : ((1 : RatComplex) : ℂ) = 1 := by
  apply Complex.ext <;> simp [toComplex]

@[simp] theorem toComplex_I : ((I : RatComplex) : ℂ) = Complex.I := by
  apply Complex.ext <;> simp [I, toComplex]

@[simp] theorem toComplex_add (z w : RatComplex) :
    ((z + w : RatComplex) : ℂ) = (z : ℂ) + (w : ℂ) := by
  apply Complex.ext <;> simp [toComplex]

@[simp] theorem toComplex_neg (z : RatComplex) :
    ((-z : RatComplex) : ℂ) = -(z : ℂ) := by
  apply Complex.ext <;> simp [toComplex]

@[simp] theorem toComplex_sub (z w : RatComplex) :
    ((z - w : RatComplex) : ℂ) = (z : ℂ) - (w : ℂ) := by
  apply Complex.ext <;> simp [toComplex]

@[simp] theorem toComplex_mul (z w : RatComplex) :
    ((z * w : RatComplex) : ℂ) = (z : ℂ) * (w : ℂ) := by
  apply Complex.ext <;> simp [toComplex]

@[simp] theorem toComplex_star (z : RatComplex) :
    ((star z : RatComplex) : ℂ) = star (z : ℂ) := by
  apply Complex.ext <;> simp [toComplex]

/-- Gaussian rationals are dense in the complex numbers. -/
theorem denseRange_toComplex : DenseRange toComplex := by
  let f : ℚ × ℚ → ℝ × ℝ := Prod.map Rat.cast Rat.cast
  have hf : DenseRange f := Rat.denseRange_cast.prodMap Rat.denseRange_cast
  let g : ℝ × ℝ → ℂ :=
    fun p => Complex.ofReal p.1 + Complex.I * Complex.ofReal p.2
  have hg : Function.Surjective g := by
    intro z
    exact ⟨(z.re, z.im), by apply Complex.ext <;> simp [g]⟩
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))
  have h := hg.denseRange.comp hf hgc
  rw [denseRange_iff_closure_range]
  rw [show Set.range toComplex =
      Set.range (fun p : ℚ × ℚ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q.re, q.im), by
        apply Complex.ext <;> simp [toComplex]⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(⟨p.1, p.2⟩ : RatComplex), by
        apply Complex.ext <;> simp [toComplex]⟩]
  exact denseRange_iff_closure_range.mp
    (by simpa [f, g, Function.comp_def] using h)

instance : Countable RatComplex :=
  Encodable.countable

end RatComplex

/-- A Gaussian-rational vector in Choi coordinates.  The product index
matches `KrausFamily.choi` directly. -/
abbrev RatChoiVec (n : ℕ) :=
  Fin (n * n) → RatComplex

instance (n : ℕ) : Encodable (RatChoiVec n) :=
  Encodable.finArrow

instance (n : ℕ) : Countable (RatChoiVec n) :=
  Encodable.countable

/-- Embed a rational Choi vector coordinatewise into `ℂ`. -/
def RatChoiVec.toComplex {n : ℕ} (v : RatChoiVec n) :
    Fin n × Fin n → ℂ :=
  fun i => v (finProdFinEquiv i)

@[simp]
theorem RatChoiVec.toComplex_add {n : ℕ} (v w : RatChoiVec n) :
    RatChoiVec.toComplex (v + w) =
      RatChoiVec.toComplex v + RatChoiVec.toComplex w := by
  funext i
  exact RatComplex.toComplex_add _ _

@[simp]
theorem RatChoiVec.toComplex_neg {n : ℕ} (v : RatChoiVec n) :
    RatChoiVec.toComplex (-v) = -RatChoiVec.toComplex v := by
  funext i
  exact RatComplex.toComplex_neg _

/-- A rational coordinate vector. -/
def RatChoiVec.single {n : ℕ} (i : Fin (n * n)) : RatChoiVec n :=
  fun j => if j = i then 1 else 0

@[simp]
theorem RatChoiVec.single_apply_self {n : ℕ} (i : Fin (n * n)) :
    RatChoiVec.single i i = 1 := by
  simp [RatChoiVec.single]

@[simp]
theorem RatChoiVec.toComplex_single {n : ℕ} (p : Fin n × Fin n) :
    (RatChoiVec.single (finProdFinEquiv p)).toComplex =
      Pi.single p (1 : ℂ) := by
  funext i
  by_cases h : i = p <;>
    simp [RatChoiVec.toComplex, RatChoiVec.single, h]

end QLambda
