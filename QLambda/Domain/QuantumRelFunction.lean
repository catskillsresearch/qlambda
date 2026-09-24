/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Domain.QuantumRelDagger
/-!
# Quantum-function preservation laws
-/

open Matrix

namespace QLambda.Domain

namespace QuantumRel

variable {X Y Z W : QuantumSet}

theorem function_eq_of_le [DecidableEq X.Atom] [DecidableEq Y.Atom]
    {F G : QuantumRel X Y} (hF : F.IsFunction) (hG : G.IsFunction)
    (hFG : F ≤ G) : F = G := by
  apply le_antisymm hFG
  have h1 : G = G.comp (id X) := (comp_id G).symm
  have h2 : G.comp (id X) ≤ G.comp (F.dagger.comp F) :=
    comp_mono_right hF.2
  have h3 : G.comp (F.dagger.comp F) = (G.comp F.dagger).comp F :=
    (assoc G F.dagger F).symm
  have h4 : G.comp F.dagger ≤ G.comp G.dagger :=
    comp_mono_right (dagger_mono hFG)
  have h5 : (G.comp F.dagger).comp F ≤ (id Y).comp F :=
    comp_mono_left F (h4.trans hG.1)
  have h6 : (id Y).comp F = F := id_comp F
  exact h1.trans_le (h2.trans (h3.le.trans (h5.trans h6.le)))

theorem IsFunction.comp [DecidableEq X.Atom] [DecidableEq Y.Atom]
    [DecidableEq Z.Atom] {S : QuantumRel Y Z} {R : QuantumRel X Y}
    (hS : S.IsFunction) (hR : R.IsFunction) :
    (S.comp R).IsFunction := by
  constructor
  · calc
      (S.comp R).comp (S.comp R).dagger
          = (S.comp R).comp (R.dagger.comp S.dagger) := by
            rw [dagger_comp]
      _ = S.comp ((R.comp R.dagger).comp S.dagger) := by
            rw [← assoc (S.comp R) R.dagger S.dagger,
              assoc S R R.dagger,
              assoc S (R.comp R.dagger) S.dagger]
      _ ≤ S.comp ((id Y).comp S.dagger) :=
            comp_mono_right (comp_mono_left S.dagger hR.1)
      _ = S.comp S.dagger := by
            rw [id_comp]
      _ ≤ id Z := hS.1
  · have hRle : R ≤ S.dagger.comp (S.comp R) := by
      calc
        R = (id Y).comp R := (id_comp R).symm
        _ ≤ (S.dagger.comp S).comp R :=
          comp_mono_left R hS.2
        _ = S.dagger.comp (S.comp R) := assoc _ _ _
    calc
      id X ≤ R.dagger.comp R := hR.2
      _ ≤ R.dagger.comp (S.dagger.comp (S.comp R)) :=
          comp_mono_right hRle
      _ = (R.dagger.comp S.dagger).comp (S.comp R) :=
          (assoc _ _ _).symm
      _ = (S.comp R).dagger.comp (S.comp R) := by
          rw [← dagger_comp]

/-- Right composition by a quantum function preserves countable meets.
This is the relational algebra lemma used in the qCPO limit proofs. -/
theorem iInf_comp_of_function [DecidableEq X.Atom] [DecidableEq Y.Atom]
    (S : ℕ → QuantumRel Y Z) (F : QuantumRel X Y) (hF : F.IsFunction) :
    (⨅ n, S n).comp F = ⨅ n, (S n).comp F := by
  apply le_antisymm
  · apply le_iInf
    intro n
    exact comp_mono_left F (iInf_le S n)
  · let T : QuantumRel X Z := ⨅ n, (S n).comp F
    have hTF : T.comp F.dagger ≤ ⨅ n, S n := by
      apply le_iInf
      intro n
      calc
        T.comp F.dagger ≤ ((S n).comp F).comp F.dagger :=
          comp_mono_left F.dagger (iInf_le (fun n => (S n).comp F) n)
        _ = (S n).comp (F.comp F.dagger) := assoc _ _ _
        _ ≤ (S n).comp (id Y) := comp_mono_right hF.1
        _ = S n := comp_id _
    change T ≤ (⨅ n, S n).comp F
    calc
      T = T.comp (id X) := (comp_id T).symm
      _ ≤ T.comp (F.dagger.comp F) := comp_mono_right hF.2
      _ = (T.comp F.dagger).comp F := (assoc _ _ _).symm
      _ ≤ (⨅ n, S n).comp F := comp_mono_left F hTF


end QuantumRel

end QLambda.Domain
