# Palomar Challenge/Comparator style

Palomar compares elaborated Lean constants, not merely mathematical
equivalence or pretty-printed declaration types. This repository's
`definition_names` list is empty. The compared holes are the two theorem
`sorry`s in `Challenge.lean`: `QLambda.Palomar.source_type_safety` and
`QLambda.Palomar.quotation_capstone`. Comparator still compares every concrete
definition reachable from those theorems, including universe names and
typeclass-instance paths inside the body. A matching parent body is
insufficient when it refers to a named child definition whose value differs.
`arxiv.md` must state these same theorem types: the reviewer reads the paper
together with the code. Run this before every submission:

```bash
scripts/palomar_preflight.sh
```

## Compared declarations

- Pin explicit universe arity (`Type u`, `Type v`) and inspect the exported
  levels; pretty-printer-generated `u_1`/`u_3` labels are presentation noise.
- Keep instance paths explicit where elaboration could choose different
  equivalent instances.
- A `theorem_names` entry must be a theorem. This repository does not put
  definition holes in `definition_names`.
- Keep concrete Challenge and Solution definition bodies structurally
  identical, including definitions reached transitively from a compared
  theorem. Do not rely on proof irrelevance to make values compare.
- `QLambda.Palomar.quotation_capstone` is typing and compile reflection.
  Ideal CQ equality is `Quotation.quotation_capstone` in
  `QuotationGeneral.lean` and is not the compared statement.
- Write order operations with explicit `@LE.le` instance paths when Challenge
  and Solution import graphs can elaborate `≤` through different parent
  structures. This repository is exposed to that failure mode wherever a
  Boolean-algebra or linear-order instance can be reached by two routes.

## Submission checklist

The preflight must confirm:

1. the full project builds;
2. compared theorem names, universe parameters, types, and transitively
   locked definition values match;
3. the two Challenge theorem holes are the only `sorry`s, and
   `formalization.yaml` records `sorry_count: 2`;
4. Solution sources contain no `sorry`;
5. Solution theorem axioms are permitted by `comparator.json`; and
6. the patch has no whitespace errors.

For day-to-day work and CI, run mechanical preflight. For a packaging
candidate (metadata / `formalization.yaml` alignment), also run the
deterministic packaging checks. Skip the LLM editorial audit until a
registry submission:

```bash
bash scripts/palomar_preflight.sh --mechanical-only   # CI / routine edits
PALOMAR_PROJECT_ROOT=$PWD python3 ../palomar-preflight/palomar_editorial_checks.py
bash scripts/palomar_preflight.sh              # mechanical + LLM audit (submission)
```

Treat a green `lake build` alone as insufficient.
