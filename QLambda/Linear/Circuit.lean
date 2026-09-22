/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.Composer.Denotation

/-!
# Typed first-order circuit normal form

This is the staging target of the linear λ-calculus.  It is intentionally
first order and has no `emit` constructor and no probabilistic, internal, or
external choice.  `branch` is ordinary classical control and probability
enters only through `measure`.
-/

namespace QLambda.Linear

open QLambda.CQ

inductive Command (q c : ℕ) where
  | skip
  | x : Fin q → Command q c
  | h : Fin q → Command q c
  | t : Fin q → Command q c
  | ry : Composer.AngleExpr → Fin q → Command q c
  | cx : Fin q → Fin q → Command q c
  | measure : Fin q → Fin c → Command q c
  | reset : Fin q → Command q c
  | store : Fin c → Composer.CExpr c → Command q c
  | seq : Command q c → Command q c → Command q c
  | branch : Composer.CExpr c → Command q c → Command q c → Command q c

namespace Command

/-- Structural compilation to the frozen Composer AST. -/
def compile {q c : ℕ} : Command q c → List (Composer.Instr q c)
  | .skip => []
  | .x w => [.gate (.x w)]
  | .h w => [.gate (.h w)]
  | .t w => [.gate (.t w)]
  | .ry θ w => [.gate (.ry θ w)]
  | .cx control target => [.gate (.cx control target)]
  | .measure qbit cbit => [.measure qbit cbit]
  | .reset qbit => [.reset qbit]
  | .store cbit e => [.store cbit e]
  | .seq A B => compile A ++ compile B
  | .branch guard yes no => [.ite guard (compile yes) (compile no)]

/- Reflect the declared Composer fragment into canonical circuit normal form. -/
mutual

  def reflectInstr {q c : ℕ} : Composer.Instr q c → Option (Command q c)
    | .gate (.x w) => some (.x w)
    | .gate (.h w) => some (.h w)
    | .gate (.t w) => some (.t w)
    | .gate (.ry θ w) => some (.ry θ w)
    | .gate (.cx control target) => some (.cx control target)
    | .measure qbit cbit => some (.measure qbit cbit)
    | .reset qbit => some (.reset qbit)
    | .store cbit e => some (.store cbit e)
    | .ite guard yes no => do
        let yes' ← reflectBlock yes
        let no' ← reflectBlock no
        pure (.branch guard yes' no')
    | _ => none

  def reflectBlock {q c : ℕ} : List (Composer.Instr q c) → Option (Command q c)
    | [] => some .skip
    | i :: is => do
        let i' ← reflectInstr i
        let is' ← reflectBlock is
        pure (.seq i' is')

end

mutual

  theorem compile_reflectInstr {q c : ℕ}
      (i : Composer.Instr q c) (C : Command q c)
      (h : reflectInstr i = some C) : C.compile = [i] := by
    cases i with
    | gate g =>
        cases g <;> simp [reflectInstr] at h <;> subst C <;> rfl
    | measure qbit cbit =>
        simp [reflectInstr] at h
        subst C
        rfl
    | reset qbit =>
        simp [reflectInstr] at h
        subst C
        rfl
    | store cbit e =>
        simp [reflectInstr] at h
        subst C
        rfl
    | ite guard yes no =>
        cases hy : reflectBlock yes with
        | none => simp [reflectInstr, hy] at h
        | some yes' =>
            cases hn : reflectBlock no with
            | none => simp [reflectInstr, hy, hn] at h
            | some no' =>
                simp [reflectInstr, hy, hn] at h
                subst C
                simp only [compile]
                rw [compile_reflectBlock yes yes' hy,
                  compile_reflectBlock no no' hn]
    | barrier qs => simp [reflectInstr] at h
    | delay duration qs => simp [reflectInstr] at h
    | switch guard cases => simp [reflectInstr] at h
    | forLoop count body => simp [reflectInstr] at h
    | whileLoop fuel guard body => simp [reflectInstr] at h
    | box label body => simp [reflectInstr] at h
    | «break» => simp [reflectInstr] at h
    | «continue» => simp [reflectInstr] at h

  theorem compile_reflectBlock {q c : ℕ}
      (is : List (Composer.Instr q c)) (C : Command q c)
      (h : reflectBlock is = some C) : C.compile = is := by
    cases is with
    | nil =>
        simp [reflectBlock] at h
        subst C
        rfl
    | cons i is =>
        cases hi : reflectInstr i with
        | none => simp [reflectBlock, hi] at h
        | some i' =>
            cases his : reflectBlock is with
            | none => simp [reflectBlock, hi, his] at h
            | some is' =>
                simp [reflectBlock, hi, his] at h
                subst C
                simp [compile, compile_reflectInstr i i' hi,
                  compile_reflectBlock is is' his]

end

/-- The normal form has exactly the target's ideal CQ meaning. -/
noncomputable def denote {q c : ℕ}
    (model : Composer.Model q c) (C : Command q c) : CQ.Sem q c :=
  Composer.denoteBlock model C.compile

theorem compile_denotation {q c : ℕ} (model : Composer.Model q c)
    (C : Command q c) :
    CQ.Eq (Composer.denoteBlock model C.compile) (C.denote model) := by
  exact CQ.Eq.refl _

/-- Exact boundary of the circuit-completeness theorem. -/
def SupportedBlock {q c : ℕ} (is : List (Composer.Instr q c)) : Prop :=
  ∃ C, reflectBlock is = some C

/-- Every supported circuit is represented by a first-order linear normal
form whose compilation is exactly the original circuit. -/
theorem circuit_complete {q c : ℕ} {is : List (Composer.Instr q c)}
    (h : SupportedBlock is) :
    ∃ C : Command q c,
      C.compile = is ∧
      ∀ model : Composer.Model q c,
        CQ.Eq (C.denote model) (Composer.denoteBlock model is) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, compile_reflectBlock is C hC, ?_⟩
  intro model
  simpa [denote, compile_reflectBlock is C hC] using
    (CQ.Eq.refl (Composer.denoteBlock model is))

/-- Well-formed supported target circuits have well-formed exact
representatives as linear circuit normal forms. -/
theorem wellFormed_circuit_complete {q c : ℕ}
    {is : List (Composer.Instr q c)}
    (hs : SupportedBlock is)
    (hwf : Composer.Block.WellFormedAt 0 is) :
    ∃ C : Command q c,
      C.compile = is ∧
      Composer.Block.WellFormedAt 0 C.compile ∧
      ∀ model : Composer.Model q c,
        CQ.Eq (C.denote model) (Composer.denoteBlock model is) := by
  obtain ⟨C, hcompile, hdenote⟩ := circuit_complete hs
  exact ⟨C, hcompile, hcompile.symm ▸ hwf, hdenote⟩

/-- Static conditions not already enforced by `Fin` indices. -/
inductive WellFormed {q c : ℕ} : Command q c → Prop where
  | skip : WellFormed .skip
  | x {w} : WellFormed (.x w)
  | h {w} : WellFormed (.h w)
  | t {w} : WellFormed (.t w)
  | ry {θ w} : WellFormed (.ry θ w)
  | cx {control target} : control ≠ target → WellFormed (.cx control target)
  | measure {qbit cbit} : WellFormed (.measure qbit cbit)
  | reset {qbit} : WellFormed (.reset qbit)
  | store {cbit e} : WellFormed (.store cbit e)
  | seq {A B} : WellFormed A → WellFormed B → WellFormed (.seq A B)
  | branch {guard yes no} :
      WellFormed yes → WellFormed no → WellFormed (.branch guard yes no)

private theorem blockWellFormed_append {q c depth}
    {A B : List (Composer.Instr q c)}
    (hA : Composer.Block.WellFormedAt depth A)
    (hB : Composer.Block.WellFormedAt depth B) :
    Composer.Block.WellFormedAt depth (A ++ B) := by
  induction A with
  | nil => simpa using hB
  | cons i is ih =>
      cases hA with
      | cons hi his =>
          exact .cons hi (ih his)

theorem compile_wellFormed {q c : ℕ} {C : Command q c}
    (hC : C.WellFormed) : Composer.Block.WellFormedAt 0 C.compile := by
  induction hC with
  | skip => exact .nil
  | x => exact .cons (.gate trivial) .nil
  | h => exact .cons (.gate trivial) .nil
  | t => exact .cons (.gate trivial) .nil
  | ry => exact .cons (.gate trivial) .nil
  | cx hne => exact .cons (.gate hne) .nil
  | measure => exact .cons .measure .nil
  | reset => exact .cons .reset .nil
  | store => exact .cons .store .nil
  | seq _ _ ihA ihB =>
      exact blockWellFormed_append ihA ihB
  | branch _ _ ihYes ihNo =>
      exact .cons (.ite ihYes ihNo) .nil

end Command

end QLambda.Linear
