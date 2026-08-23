[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/qlambda/build.yml?label=Lean%204)](https://github.com/catskillsresearch/qlambda/actions/workflows/build.yml)

# qlambda

Denotational semantics of an untyped quantum λ-calculus in the category
**ωQVA** (quantum-valuation approximable domains). Lean 4 library on top
of a vendored [`scott1972`](https://github.com/catskillsresearch/scott1972)
formalization of Dana Scott, *Continuous Lattices* (LNM 274).

The **Palomar statement of record** is the capstone

`omegaQVA_quantum_domain_equation_solved` :

the inverse limit `D_∞` of the quantum tower `D_{n+1} = [D_n → Q(D_n)]`
is an object of ωQVA and is order-isomorphic to its own function space
(`D_∞ ≅ [D_∞ → Q(D_∞)]`), together with the supporting surface
`qDInf_isOmegaQVA` and `finitelySeparated_wayBelow`.

Narrative: `arxiv.md`. Palomar metadata: `comparator.json`,
`formalization.yaml`. Vendor / attribution: `PROVENANCE.md`,
`vendor/FROZEN.txt`.

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `QLambda`, `Challenge`, and `Solution`.
`Challenge.lean` may contain `sorry`. `Solution.lean` re-exports the
sorry-free `Quantum/` proofs.

Palomar type check (green `lake build` is not enough):

```bash
bash scripts/compare_challenge_solution_types.sh
```

ArXiv / Zenodo: `bash scripts/build_arxiv_pdf.sh` and
`bash scripts/package_zenodo.sh` (see `ZENODO.md`).

### Provenance, Attribution & Third-Party Software Statement

1. **Original Mathematical Formalizations (Author: Lars Warren Ericson):**
   * The core formalization of D. S. Scott's 1972 *Continuous Lattices* in `vendor/scott1972/` is the original work of Lars Warren Ericson (Catskills Research, 2026); the remote remains [`scott1972`](https://github.com/catskillsresearch/scott1972).
   * The non-commutative operator extension (ω**QVA**), spectrahedral state-space formalization, and quantum domain equation in `Quantum/` were designed and mechanized by Lars Warren Ericson.

2. **Literature (not a Lean dependency):**
   * Chen, Kou, and Lyu, *Finite-valuation approximable structures* (arXiv:2608.03073, 2026), in `sources/`. Saturation lemmas are mechanized in `Quantum/Saturation.lean`.

3. **Literature Citations:**
   * Foundational domain theory: D. S. Scott (1972, LNM 274); M. B. Smyth & G. D. Plotkin (1982).
   * Probabilistic resolution of Jung–Tix: Y. Chen, H. Kou, Z. Lyu (arXiv:2608.03073, 2026).
   * Quantum process calculi and programming: P. Selinger & B. Valiron (2009); M. Ying (2016).

4. **AI Tooling Disclosure:**
   * Large language models (Cursor Grok 4.6 and others) were used as assistive tools for scaffolding, LaTeX/Markdown, and literature cross-checking. All formal Lean 4 proof scripts remain the author's responsibility; generated Lean is provisional until it compiles under the pinned toolchain.
