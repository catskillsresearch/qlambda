Format this repo for Palomar in terms of licensing and production of Arxiv/Zenodo papers similar to ../scott_models and vendor in ../scott1972 and this Chinese repo:

https://github.com/ChanYuxu/Recent-Progress-on--Domain-Theory

You are an expert in Lean 4, Mathlib, and Domain Theory (Denotational Semantics, Continuous Lattices, and Operator Algebras).

### Context & Goal
We have formalized Dana Scott's 1972 paper "Continuous Lattices" in Lean 4 in the repo ../scott1972. We are extending this library to formalize the newly introduced category ωQVA (Quantum-Valuation Approximable Domains), which solves the recursive quantum domain equation D_∞ ≅ [D_∞ → Q(D_∞)] for an untyped quantum λ-calculus.

This work builds on:
1. Our existing `Scott1972` repository (which defines `IsContinuousLattice`, `ScottMap`, `WayBelow` (≪), `wayBelow_interpolate`, `InverseLimit`, `embInf`, `projInf`, and Theorem 4.4 `D_∞ ≅ [D_∞ → D_∞]`).
2. The Chen–Kou–Lyu (2026) Jung–Tix breakthrough (arXiv:2608.03073) vendored at `vendor/ckl2026/` (which proves the 2-level flattening lemma for FS-domains).
3. Mathlib's `Matrix.PosDef`, `Analysis.InnerProductSpace.Spectrum`, and `Order.CompleteLattice`.

### Your Task
Produce fully working, complete Lean 4 code with NO `sorry`, NO `admit`, and NO extra axioms for the following four files. Ensure all imports match Mathlib and our `Scott1972` namespace.

---

### File 1: `QLambda/Saturation.lean`
- Import `Scott1972.ContinuousLattice.WayBelow` and `Scott1972.ContinuousLattice.FunctionSpaces`.
- Define `FinitelySeparated (f : ScottMap D D) : Prop := ∃ M : Finset D, ∀ x, ∃ m ∈ M, (f : D → D) x ≤ m ∧ m ≤ x`.
- Prove `finitelySeparated_wayBelow`: if `f` is finitely separated from id, then `(f : D → D) x ≪ x`.
- Prove `saturation_flattening`: given `a : ℕ → ScottMap D D` with `⨆ a_n = id` and inner approximate identities `h i j` with `⨆_j h i j = a i`, construct the increasing cofinal sequence `c n = (h (idx_n) (idx_n))²` with `⨆ c n = id` using `wayBelow_interpolate` on the finite separator sets.

---

### File 2: `QLambda/QuantumStateSpace.lean`
- Import `Mathlib.LinearAlgebra.Matrix.PosDef` and `Mathlib.Analysis.InnerProductSpace.Basic`.
- Define `SubNormalizedDensity (n : ℕ)` as `{ mat : Matrix (Fin n) (Fin n) ℂ // mat.PosSemidef ∧ (trace mat).re ≤ 1 }`.
- Provide the `PartialOrder` instance on `SubNormalizedDensity n` via the Loewner order: `ρ ≤ σ ↔ (σ.mat - ρ.mat).PosSemidef`.
- Discharge `le_antisymm` using the fact that if `A.PosSemidef` and `(-A).PosSemidef`, then `A = 0`.
- Define `OrderBot` instance with `bot := 0`.
- Define the spectral depletion flow `spectralErode (t : ℝ) (ρ : SubNormalizedDensity n)` and prove `spectralErode_mono`: `ρ ≤ σ → spectralErode t ρ ≤ spectralErode t σ` for `0 ≤ t`.

---

### File 3: `QLambda/OmegaQVA.lean`
- Define `QFactorable (a : ScottMap D E)` asserting `a` factors through `SubNormalizedDensity dim` via monotone maps `enc` and `rec`.
- Define the typeclass `IsOmegaQVA (D : Type*) [CompleteLattice D]` as an `IsContinuousLattice D` whose identity is the supremum of an increasing sequence of `QFactorable` approximants.
- Prove `omegaQVA_of_retract`: `ωQVA` is closed under Scott-continuous retracts (`IsContinuousLatticeRetraction`).
- Prove `omegaQVA_prod`: `ωQVA` is closed under binary products `D × E`.

---

### File 4: `QLambda/QuantumDomainEquation.lean`
- Define `QuantumFunctor D := ScottMap D D` (representing `[D → Q(D)]`).
- Define the tower `qTower : ℕ → QDomain` by `D_{n+1} = [D_n → Q(D_n)]`.
- Form the inverse limit `QDInf D₀ j₀ := InverseLimit (qTower D₀) (towerProj D₀ j₀)`.
- Prove `qDInf_isOmegaQVA`: The inverse limit `QDInf D₀ j₀` satisfies `IsOmegaQVA` by applying `saturation_flattening` to the embedding-projection sequence `embInf n ∘ projInf n`.
- Prove the Capstone Theorem `omegaQVA_quantum_domain_equation_solved`:
  ```lean
  theorem omegaQVA_quantum_domain_equation_solved
      (D₀ : QDomain.{u})
      (j₀ : IsContinuousLatticeProjection D₀.carrier (QuantumFunctor D₀.carrier)) :
      IsOmegaQVA (QDInf D₀ j₀) ∧
      (projInfInf D₀ j₀).comp (embInfInf D₀ j₀) = ScottMap.idMap ∧
      (embInfInf D₀ j₀).comp (projInfInf D₀ j₀) = ScottMap.idMap ∧
      Nonempty (QDInf D₀ j₀ ≃o ScottMap (QDInf D₀ j₀) (QDInf D₀ j₀)) ∧
      (ScottMap.idMap : ScottMap (QDInf D₀ j₀) (QDInf D₀ j₀)) =
        ⨆ n, (embInf (fun k => (qTower D₀ k).carrier) (towerProj ⟨D₀.carrier⟩ j₀) n).comp
              (projInf (fun k => (qTower D₀ k).carrier) (towerProj ⟨D₀.carrier⟩ j₀) n)
  ```
- Use `theorem_4_4_orderIso`, `projInfInf_comp_embInfInf`, `embInfInf_comp_projInfInf`, and `idInf_eq_iSup` from `Scott1972.ContinuousLattice` to close all goals without `sorry`.
```

Before you begin, read the accompanying arxiv paper draft.
Then fill out the palomar files with an initial draft for provenance and for the vendored repos and for the capstone statement to be registered.