# arXiv submission metadata (typed linear qlambda formalization)

Copy-paste fields for the arXiv web form. Regenerate the PDF and zip with
`bash scripts/build_arxiv_pdf.sh` before uploading `dist/arxiv_submit.zip`.

## Title (plain text for arXiv web form)

The metadata field must be **ASCII plain text** (no `$`, `\`, or Unicode
dashes).

```
Domain Semantics and Circuit Completeness for a Typed Linear Quantum Lambda-Calculus Formalized in Lean 4
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

The source archive should ship the active `Domain`, `Linear`, reusable
CP/CQ/Composer modules, and the exact theorem index. Legacy modules are not
part of the paper's claimed surface.
