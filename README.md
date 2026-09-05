[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/qlambda/build.yml?label=Lean%204)](https://github.com/catskillsresearch/qlambda/actions/workflows/build.yml)

# qlambda

Lean 4 development toward denotational semantics of an untyped quantum
λ-calculus using **ωQVA** (quantum-valuation approximable domains) and
finite CP instruments. The library builds on top
of a vendored [`scott1972`](https://github.com/catskillsresearch/scott1972)
formalization of Dana Scott, *Continuous Lattices* (LNM 274).

The **Palomar compared statement of record** is the canonical-base domain capstone

`canonical_omegaQVA_quantum_domain_equation_solved`:

for every bundled `QuantumPowerModel` `M`, start from the canonical one-point
ωQVA domain. The canonical stage-zero pair embeds the point as the bottom
function and has bonding retraction `[PUnit → Q(PUnit)] ↠ PUnit`. The inverse
limit `D_∞` of `D_{n+1} = [D_n → Q(D_n)]` lies in ωQVA; the constructed maps
`qEmbInfInf : D_∞ → [D_∞ → Q(D_∞)]` and
`qProjInfInf : [D_∞ → Q(D_∞)] → D_∞` are mutual inverses; `D_∞` is
order-isomorphic to that function space; and Scott's inverse-limit identity
holds on the tower.

The wider repository retains the conditional theorem
`omegaQVA_quantum_domain_equation_solved M D₀ j₀`, where `j₀` is a supplied
embedding–retraction pair with `incl : D₀ → [D₀ → Q(D₀)]` and bonding
`retr : [D₀ → Q(D₀)] ↠ D₀`. It also proves supporting lemmas, the concrete
`QLambda.TTContinuation.canonical_omegaQVA_quantum_domain_equation_solved n`,
and bounded hardware adequacy capstones. These are indexed in `THEOREMS.md`
but are not selected by `comparator.json` for this Palomar entry.

A concrete fixed-register instance is now constructed as
`TTContinuation.model n`, with carrier
`TTContinuationPower n D = [[D → TTResult n] → TTResult n]`.
`TTPhysicalEmbedding.embed` maps Kraus-presented finite
trace-nonincreasing instruments into this carrier. It preserves return
exactly, agrees with finite map and bind on finitely presented result
continuations, and recovers explicitly Scott-represented finitary TT
tests from embedding order.

The final hardware adequacy capstones are
`closed_stuck_free_presented_channelTreeCompleteness` and
`closed_stuck_free_presented_token_adequacy`. They apply exactly to closed
programs carrying a `ClosedStuckFreeCoverage` witness, including the
restricted ordinary and recursive lambda applications with an external
choice argument represented by `RestrictedExternApplication`.

## Status and boundaries

The domain construction is complete at its stated interface:

- ωQVA Cartesian closure and inverse-limit domain equation;
- the fixed-register continuation quantum power and monad;
- physical finite-instrument embedding and finite monad compatibility;
- represented-test refinement recovery and the directed-supremum
  obstruction to a finite-image Scott retract.

The core language layer is now implemented: syntax is parameterized by
closed quantum primitives and includes recursive abstractions;
`QLambda.interp` maps every term compositionally into `Q(D_∞)`, with pure
values lifted by monadic `unit`, call-by-value application implemented by
Scott-continuous `bind`, and recursion interpreted by Scott `fix`.
Environment lookup/update, constructor equations, value purity,
compositional Scott continuity, recursive unfolding, substitution and
β-equations, and operational soundness are proved. The concrete TT model
keeps probabilistic, internal, and external choice distinct. The hardware
result is presented channel-tree completeness and token adequacy at the
named `ClosedStuckFreeCoverage` boundary, not an unrestricted theorem for
every closed term or arbitrary Scott continuation.

See `THEOREMS.md` for the compact theorem/file index and exact boundaries.
See `arxiv.md` for the proof journey, definitions, theorem statements,
examples, and narrative status.

The formalized result is the quantum `ωQVA` domain theorem and its language
and hardware interfaces. Chen–Kou–Lyu `ωFVA` / Jung–Tix is motivating
classical literature and is not re-formalized here in full. The Qiskit
material in `arxiv.md` is an operational comparison through shared CP
denotations, not a compiler or verified Qiskit equivalence.

Narrative: `arxiv.md`. Theorem index: `THEOREMS.md`. Palomar metadata:
`comparator.json`, `formalization.yaml`, `docs/PALOMAR_STYLE.md`.
Vendor / attribution: `PROVENANCE.md`, `vendor/FROZEN.txt`.

## Palomar packaging

Local mechanical readiness (CI runs this on every push):

```bash
bash scripts/palomar_preflight.sh --mechanical-only
```

Before registry submission, run the full gate (mechanical checks plus
vendored-policy sync and Cursor editorial audit):

```bash
bash scripts/palomar_preflight.sh
```

Mechanical green means Challenge and Solution types match under Comparator
rules and Solution sources contain no `sorry`. It does **not** assign a
Palomar registry ID. Actual registration requires a public GitHub repository,
a full 40-character commit SHA, the root project path, and explicit selection
of `comparator.json` at [submit.palomar-registry.org](https://submit.palomar-registry.org/).

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `QLambda`, `Challenge`, and `Solution`.
`Challenge.lean` may contain `sorry`. `Solution.lean` re-exports the
sorry-free compared proofs; unfinished semantics modules are outside
that compared surface.

Palomar type check (green `lake build` is not enough):

```bash
bash scripts/palomar_preflight.sh --mechanical-only
```

Or the underlying Comparator diff alone:

```bash
bash scripts/palomar_preflight.sh --mechanical-only
```

ArXiv / Zenodo: `bash scripts/build_arxiv_pdf.sh` and
`bash scripts/package_zenodo.sh` (see `ZENODO.md`).

### Provenance, Attribution & Third-Party Software Statement

1. **Original Mathematical Formalizations (Author: Lars Warren Ericson):**
   * The core formalization of D. S. Scott's 1972 *Continuous Lattices* in `vendor/scott1972/` is the original work of Lars Warren Ericson (Catskills Research, 2026); the remote remains [`scott1972`](https://github.com/catskillsresearch/scott1972).
   * The non-commutative operator extension (ω**QVA**), spectrahedral state-space formalization, and quantum domain equation in `QLambda/` were designed and mechanized by Lars Warren Ericson.

2. **Literature (not a Lean dependency):**
   * Chen, Kou, and Lyu, *Finite-valuation approximable structures* (arXiv:2608.03073, 2026), in `sources/`. Saturation lemmas are mechanized in `QLambda/Saturation.lean`.

3. **Literature Citations:**
   * Foundational domain theory: D. S. Scott (1972, LNM 274); M. B. Smyth & G. D. Plotkin (1982).
   * Probabilistic resolution of Jung–Tix: Y. Chen, H. Kou, Z. Lyu (arXiv:2608.03073, 2026).
   * Quantum process calculi and programming: P. Selinger & B. Valiron (2009); M. Ying (2016).

4. **AI Tooling Disclosure:**
   * Large language models (Cursor Grok 4.6, GPT-5.6 Sol Medium, and others) were used as assistive tools for scaffolding, proof exploration, LaTeX/Markdown, and literature cross-checking. All formal Lean 4 proof scripts remain the author's responsibility; generated Lean is provisional until it compiles under the pinned toolchain.
