/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Order.Antisymmetrization
import QLambda.QuantumInstrument
import QLambda.ScottLowerSet
import QLambda.Composer.MatrixSemantics

/-!
# Completed finite-dimensional quantum operations

Finite Kraus lists are presentations, not semantic maps: two lists can
denote the same completely positive map.  We first antisymmetrize the
intrinsic Choi order, and only then take the Scott-lower completion.
Consequently equality in `CompletedCP` is presentation independent and
the carrier is a complete lattice (hence a pointed ωCPO).

This module deliberately imports neither `QuantumPower` nor `OmegaQVA`.
-/

namespace QLambda.Domain

open scoped MatrixOrder

/-- A wrapper giving finite Kraus presentations their semantic CP
refinement order rather than any structural list order. -/
structure CPPresentation (n m : ℕ) where
  kraus : KrausFamily n m

noncomputable instance instPreorderCPPresentation (n m : ℕ) :
    Preorder (CPPresentation n m) where
  le := fun K L => KrausFamily.ResidualRefines K.kraus L.kraus
  lt := fun K L =>
    KrausFamily.ResidualRefines K.kraus L.kraus ∧
      ¬KrausFamily.ResidualRefines L.kraus K.kraus
  le_refl K := KrausFamily.residualRefines_refl K.kraus
  le_trans _ _ _ := KrausFamily.residualRefines_trans
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

/-- A finite CP presentation modulo equality of its intrinsic Choi map. -/
abbrev SemanticCP (n m : ℕ) :=
  Antisymmetrization (CPPresentation n m) (· ≤ ·)

/-- The Scott completion of finite-dimensional CP maps. -/
abbrev CompletedCP (n m : ℕ) :=
  ScottLowerSet.Carrier (SemanticCP n m)

namespace CompletedCP

variable {n m ℓ : ℕ}

/-- Embed a finite Kraus presentation into the completed CP hom. -/
noncomputable def ofKraus (K : KrausFamily n m) : CompletedCP n m :=
  ScottLowerSet.principal
    (toAntisymmetrization (· ≤ ·) ⟨K⟩)

/-- The embedded zero CP map is the principal ideal of the empty
Kraus presentation. -/
noncomputable def zero : CompletedCP n m :=
  ofKraus KrausFamily.zero

/-- The embedded identity channel. -/
noncomputable def identity (n : ℕ) : CompletedCP n n :=
  ofKraus (KrausFamily.identity n)

theorem ofKraus_mono {K L : KrausFamily n m}
    (hKL : KrausFamily.ResidualRefines K L) :
    ofKraus K ≤ ofKraus L := by
  change (⟨K⟩ : CPPresentation n m) ≤ ⟨L⟩ at hKL
  exact ScottLowerSet.principal_mono
    (toAntisymmetrization_mono hKL)

/-- Equal CP maps have equal principal embeddings. -/
theorem ofKraus_eq_of_semEq {K L : KrausFamily n m}
    (hKL : KrausFamily.SemEq K L) :
    ofKraus K = ofKraus L := by
  apply le_antisymm
  · exact ofKraus_mono (KrausFamily.residualRefines_of_semEq hKL)
  · exact ofKraus_mono
      (KrausFamily.residualRefines_of_semEq
        (KrausFamily.applySemEq_symm hKL))

/-- Finite postcomposition is monotone before completion. -/
theorem ofKraus_comp_mono_left (M : KrausFamily m ℓ)
    {K L : KrausFamily n m} (hKL : KrausFamily.ResidualRefines K L) :
    ofKraus (KrausFamily.comp M K) ≤
      ofKraus (KrausFamily.comp M L) :=
  ofKraus_mono (KrausFamily.residualRefines_comp_left M hKL)

/-- Finite precomposition is monotone before completion. -/
theorem ofKraus_comp_mono_right (M : KrausFamily ℓ n)
    {K L : KrausFamily n m} (hKL : KrausFamily.ResidualRefines K L) :
    ofKraus (KrausFamily.comp K M) ≤
      ofKraus (KrausFamily.comp L M) :=
  ofKraus_mono (KrausFamily.residualRefines_comp_right M hKL)

/-- Embedded finite composition is associative. -/
theorem ofKraus_comp_assoc {r : ℕ}
    (M : KrausFamily ℓ r) (L : KrausFamily m ℓ)
    (K : KrausFamily n m) :
    ofKraus (KrausFamily.comp M (KrausFamily.comp L K)) =
      ofKraus (KrausFamily.comp (KrausFamily.comp M L) K) := by
  rw [KrausFamily.comp_assoc]

/-- A finite instrument embeds each CP branch in the completed hom. -/
structure Instrument (n m outcomes : ℕ) where
  branch : Fin outcomes → CompletedCP n m

namespace Instrument

/-- Embed a proof-carrying finite quantum instrument. -/
noncomputable def ofQuantumInstrument
    {outcomes : ℕ} (Φ : QuantumInstrument n m outcomes) :
    Instrument n m outcomes where
  branch o := ofKraus (Φ.branch o)

end Instrument

/-- The canonical computational-basis measurement is a concrete
two-outcome completed instrument. -/
noncomputable def measure {q : ℕ} (w : Fin q) :
    Instrument (CQ.QDim q) (CQ.QDim q) 2 :=
  Instrument.ofQuantumInstrument (Composer.measure w)

/-- The canonical reset channel embedded in the completion. -/
noncomputable def reset {q : ℕ} (w : Fin q) :
    CompletedCP (CQ.QDim q) (CQ.QDim q) :=
  ofKraus (Composer.reset w).kraus

end CompletedCP

end QLambda.Domain
