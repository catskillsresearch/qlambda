# CMU School of Computer Science technical report

Publication checklist for *Mechanized Denotation and Circuit Staging for an
N-Bounded Linear Quantum λ-Fragment in Lean 4*.

## Report metadata

- **Series:** Carnegie Mellon University School of Computer Science Technical
  Report
- **Number:** `CMU-CS-26-XXX` (placeholder)
- **Date:** September 2026
- **Author:** Lars Warren Ericson
- **Institutional address:** School of Computer Science, Carnegie Mellon
  University, Pittsburgh, PA 15213
- **arXiv cross-archive:** `cs.LO` / `math.LO` / `quant-ph`

Lars Warren Ericson is an independent researcher, d/b/a Catskills Research
Company (`lars.ericson@catskillsresearch.com`).

## Build

```bash
lake exe cache get
lake build
bash scripts/build_arxiv_pdf.sh
```

The build produces:

- `arxiv.pdf` — CMU-formatted report PDF (titlepage, abstract, **table of
  contents**, **list of figures**, body);
- `arxiv.tex` — generated complete LaTeX source (gitignored);
- `lean-listings/` and `figures/` — generated report inputs (gitignored);
- `dist/arxiv_submit.zip` — pdfLaTeX-ready cross-archive bundle, including
  `cmu-titlepage2.sty`.

The title page uses the report-mode layout from CMU's `cmu-titlepage2.sty`
(same packaging as `../scott1964`). Front matter after `\maketitle` is:

```tex
\tableofcontents
\clearpage
\listoffigures
\clearpage
```

## Before public release

1. Replace every `CMU-CS-26-XXX` occurrence with the assigned CMU report
   number.
2. Confirm the September 2026 date, author affiliation footnote, and
   correspondence email.
3. Run `lake build` and `bash scripts/build_arxiv_pdf.sh`.
4. Inspect the cover, keywords page, abstract, table of contents, list of
   figures, numbered Mermaid figures, acknowledgments, and references.
5. Upload `dist/arxiv_submit.zip` only after deleting prior arXiv submission
   files so the source set is replaced rather than merged.
