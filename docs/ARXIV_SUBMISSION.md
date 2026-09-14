# arXiv submission metadata (QLambda / ωQVA formalization)

Copy-paste fields for the arXiv web form. Regenerate the PDF and zip with
`bash scripts/build_arxiv_pdf.sh` before uploading `dist/arxiv_submit.zip`.

## Title (plain text for arXiv web form)

The `#` title in `arxiv.md` uses LaTeX (`$\lambda$`) and an en-dash (`Jung–Tix`);
the metadata field must be **ASCII plain text** (no `$`, `\`, or Unicode dashes).

```
Finite-Valuation Approximable Structures, Quantum lambda-Calculus, and the Jung-Tix Problem: Semantics and Formal Verification in Lean 4
```

The PDF title still comes from `arxiv.md` / `\title{...}` with proper math and typography.

## Abstract (plain text, under 1920 characters)

See the `## Abstract` section in `arxiv.md` (same text appears in the PDF
`\begin{abstract}` block).

## Categories

| System | Recommendation |
| --- | --- |
| **arXiv primary** | `cs.LO` (Logic in Computer Science) |
| **arXiv secondary** | `quant-ph` (Quantum Physics); `math.LO` (Logic) |
| **Optional arXiv** | `cs.PL` (Programming Languages) |

**MSC 2020** (semicolon-separated for arXiv): `06B35; 68Q55; 81P68; 68V20`

- `06B35` — Continuous lattices and posets
- `68Q55` — Semantics of programming languages
- `81P68` — Quantum computation
- `68V20` — Formalization of mathematics (Lean / proof assistants)

**ACM 1998** (semicolon-separated): `F.3.2; F.4.1; D.3.1; I.2.3`

- `F.3.2` — Semantics of programming languages
- `F.4.1` — Mathematical logic
- `D.3.1` — Formal definitions and theory of programming languages
- `I.2.3` — Deduction and theorem proving

## Compiler

pdfLaTeX (`00README.json` sets `"compiler": "pdflatex"`).

## Repository

https://github.com/catskillsresearch/qlambda

Note: vendored `vendor/scott1972` is indexed in Appendix A but not duplicated in the
arXiv zip; the zip ships `QLambda/` sources for the compared development.
