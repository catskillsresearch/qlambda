# Provenance

This Palomar snapshot is the quantum-domain companion to
[`scott1972`](https://github.com/catskillsresearch/scott1972)
(Lean 4 mechanization of Dana Scott, *Continuous Lattices*, LNM 274).
The 1972 library is copied into `vendor/scott1972` at the frozen SHA in
`vendor/FROZEN.txt` so a preservation fork of `qlambda` contains the
complete development. The remote remains the 1972 home.

## Author work

The ω**QVA** type surface, Loewner state space, saturation flattening
used for the quantum bilimit, and the capstone
`omegaQVA_quantum_domain_equation_solved` are original Lean of
Lars Warren Ericson (Catskills Research Company, 2026). They extend
Scott 1972 inverse limits (`embInf`, `projInf`, Theorem 4.4) from
`D_∞ ≅ [D_∞ → D_∞]` to the quantum functor `[D → Q(D)]`.

## Vendored third-party mathematics (`vendor/ckl2026/`)

Chen, Kou, and Lyu, *Finite-valuation approximable structures*
(arXiv:2608.03073, 2026) supply the classical saturation pattern
(Lemmas 6.8–6.10: finite separation ⇒ `f(x) ≪ x`; 2-level flattening of
squares). The GitHub URL recorded in earlier notes,

`https://github.com/ChanYuxu/Recent-Progress-on-Domain-Theory`,

returned **404** on 2026-08-22; no public Lean tree was obtainable.
This snapshot therefore vendors the published lemmas as a literature
artifact (`vendor/ckl2026/`) and mechanizes them in
`Quantum/Saturation.lean` under Apache-2.0, with attribution to the
authors of the mathematics.

## Related remotes (not vendored)

| Remote | Role |
| --- | --- |
| [`scott1972`](https://github.com/catskillsresearch/scott1972) | Continuous lattices; Theorem 4.4 |
| [`scott_models`](https://github.com/catskillsresearch/scott_models) | Presentation bridges (1972 / 1980 / 1982) |
| arXiv:2608.03073 | Chen–Kou–Lyu ω**FVA** / Jung–Tix |
