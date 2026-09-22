# Novelty audit for the typed linear qlambda paper

This file records the evidence behind novelty wording in `arxiv.md`.  It is a
working bibliographic audit, not a claim of priority.

## Sources checked

1. Andre Kornell, *Quantum sets*, Journal of Mathematical Physics 61 (2020),
   arXiv:1804.00581.
2. Andre Kornell, Bert Lindenhovius, and Michael Mislove, *Quantum CPOs*,
   arXiv:2109.02196.
3. Kornell, Lindenhovius, and Mislove, *Categories of quantum cpos*,
   Mathematical Structures in Computer Science (2026),
   arXiv:2406.01816; DOI: 10.1017/S096012952610053X.
4. Nik Weaver, *Quantum relations*, Memoirs of the AMS 215(1010), 2012.
5. The quantaloid presentation developed by
   Jenča and Lindenhovius, *Monoidal Quantaloids* (2025).
6. Kornell, Lindenhovius, and Mislove, *A Category of Quantum Posets*,
   Indagationes Mathematicae 34 (2023).
7. Lindenhovius, Mislove, and Zamdzhiev, *LNL-FPC* (LMCS 2021), and
   Rios and Selinger, *A Categorical Model for a Quantum Circuit Description
   Language* (2017).

## Results already claimed in the literature

The paper must not describe the following mathematical statements as new:

- quantum sets and quantum relations form a dagger-compact category;
- quantum-relation homs are enriched over complete modular ortholattices;
- quantum sets and quantum functions form a symmetric monoidal closed
  category;
- `Set -> qSet` is strong monoidal and has a right adjoint;
- `qPOS` is order enriched, complete, cocomplete, and monoidal closed;
- `POS -> qPOS` is strong monoidal and has a right adjoint;
- `qCPO` is CPO-enriched and symmetric monoidal closed;
- `CPO -> qCPO` is strong monoidal and has a right adjoint;
- pointed strict quantum CPOs are algebraically compact and form the linear
  side of an LNL model.

The 2021 paper states these in Theorems 4.6, 5.6, and 5.10 and Propositions
5.8--5.9. The later *Categories of quantum cpos* account supplies explicit
constructions. *Monoidal Quantaloids* proves the stronger arbitrary-join and
dagger-compact quantaloid results for the atomic matrix presentation.
*A Category of Quantum Posets* proves the codomain-order characterization and
function-order laws. Thus omitted proofs in the 2021 paper are not evidence
that the mathematical results are new.

## What this repository can claim

Subject to a final search for other proof assistants, the following is safe:

- a Lean 4 formalization of the exact finite-dimensional matrix/subspace
  presentation used here;
- kernel-checked proofs of identity, associativity, dagger composition,
  function composition, complete-lattice structure, and bilateral
  countable-join preservation for the chosen representation;
- a kernel-checked construction of tensor, internal hom, coherence maps, and
  the concrete ordinary `Set ⊣ qRel` LNL adjunction (`quantumLNL`);
- a separate kernel-checked category of quantum CPOs and Scott-continuous
  quantum functions;
- a typed source metatheory, finite CP/instrument meanings, staging, and
  two-wire circuit reflection as separately checked layers.

These are claims of new formal proofs or integration, not currently claims
that the underlying mathematical theorems are new.

The direct `Set ⊣ qRel` instance is an ordinary compact-closed relation model,
not the published recursive qCPO LNL construction. The literature-supported
route is the lifted-qCPO Kleisli model
`CPO → qCPO → qCPO⊥!`. The repository must not describe `quantumLNL` as a
formalization of that model or use it as evidence for recursive source
denotation.

The selected completion route is a typed submodel of the CP-enriched
superoperator-module presheaf semantics of Tsukada and Asada. Their
presheaf model, exponential, recursive types, soundness, adequacy, and full
abstraction are published mathematical results. The repository may claim a
new Lean formalization and integration only after the corresponding
declarations compile; it must not claim those categorical results as new.

## Candidate genuinely new results

Any mathematical novelty claim must name a theorem absent from the sources
above and explain why it is not merely a representation-level lemma.  The
following remain candidates until the corresponding Lean declarations and a
broader search exist:

- extension of the checked two-wire circuit-completeness theorem to the full
  structured Composer/OpenQASM fragment and to an instantiated higher-order
  source denotation.

If none survives the search, the abstract should say “new formal proofs” and
“first mechanized integration,” not “new mathematical theorem.”

## Wording rule

Use “to our knowledge” for priority language.  Never infer novelty merely from
an omitted proof: *Quantum CPOs* explicitly says that most proofs were omitted
for space, while still stating the categorical theorems.

General state preparation, reset, and arbitrary CP instruments are not Weaver
quantum functions. Their integration with the published qCPO LNL model is not
an available corollary; it requires additional probabilistic/CP monadic
structure or a different CP-enriched model. This is a model boundary, not a
novelty claim.
