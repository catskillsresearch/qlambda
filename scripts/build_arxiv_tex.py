#!/usr/bin/env python3
r"""Convert arxiv_with_code.md to arxiv.tex (arXiv-ready).

Pipeline:
  1. Drop the GitHub-only navigation preamble (auto-gen note, document map, file index).
  2. Lift the `## Abstract` section into a LaTeX \begin{abstract}.
  3. Demote the Appendix-A structural headings so LaTeX numbers everything once, then
     insert \\appendix before the combined Lean-source appendix.
  4. Strip manual section numbers (any depth, e.g. `1.`, `1.3`, `5.1`) so LaTeX does
     the numbering and we never get duplicates like "5.1 5.1".
  5. Replace fenced code with \\lstinputlisting blocks (ASCII-sanitized for arXiv pdfLaTeX).
  5b. Render ```mermaid blocks to PNG via mermaid-cli (mmdc) for arXiv pdfLaTeX.
      Wrap each diagram in a numbered figure; a following `**Figure.** caption`
      line (or `mermaid caption="..."` fence header) becomes the LaTeX caption.
  6. Inject AI model-card acknowledgements from `scripts/ai_model_cards.py` (before HTML-comment strip).
  7. pandoc → LaTeX, then splice the listing/math/figure placeholders back in.
  8. Insert CMU front-matter \\tableofcontents and \\listoffigures after \\maketitle.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
from ai_model_cards import inject_model_cards
from lean_listing_sanitize import chunk_line_ranges, sanitize_lean_for_arxiv

SRC = ROOT / "arxiv_with_code.md"
OUT = ROOT / "arxiv.tex"
PREAMBLE = SCRIPTS / "tex_preamble_arxiv.tex"
LISTINGS_DIR = ROOT / "lean-listings"
FIGURES_DIR = ROOT / "figures"
PUPPETEER_CONFIG = SCRIPTS / "puppeteer-config.json"
LISTING_CHUNK_LINES = 400

AUTHOR = "Lars Warren Ericson"
COMPANY = "Catskills Research Company"
GITHUB_URL = r"https://github.com/catskillsresearch/qlambda"
ORCID = "0000-0001-8299-9361"
EMAIL = "lars.ericson@catskillsresearch.com"
REPORT_NUMBER = "CMU-CS-26-XXX"
REPORT_DATE = "September 2026"


def find_chrome() -> str | None:
    env = os.environ.get("PUPPETEER_EXECUTABLE_PATH")
    if env and Path(env).exists():
        return env
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def render_mermaid(code: str, idx: int) -> str:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    mmd_path = FIGURES_DIR / f"figure-{idx:03d}.mmd"
    png_path = FIGURES_DIR / f"figure-{idx:03d}.png"
    mmd_path.write_text(code.strip() + "\n", encoding="utf-8")

    mmdc = shutil.which("mmdc")
    if not mmdc:
        raise RuntimeError(
            "mermaid-cli (mmdc) not found; install with "
            "`npm install -g @mermaid-js/mermaid-cli`"
        )
    env = os.environ.copy()
    chrome = find_chrome()
    if chrome:
        env["PUPPETEER_EXECUTABLE_PATH"] = chrome
    cmd = [mmdc, "-i", str(mmd_path), "-o", str(png_path), "-b", "white"]
    if PUPPETEER_CONFIG.is_file():
        cmd += ["-p", str(PUPPETEER_CONFIG)]
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)
    if proc.returncode != 0 or not png_path.is_file():
        sys.stderr.write(proc.stdout + "\n" + proc.stderr + "\n")
        raise RuntimeError(f"mmdc failed to render figure {idx}")
    return png_path.relative_to(ROOT).as_posix()


def extract_title() -> str:
    first = (ROOT / "arxiv.md").read_text(encoding="utf-8").splitlines()[0]
    title = first[2:].strip() if first.startswith("# ") else first.strip()
    title = re.sub(r"\*([^*]+)\*", r"\\emph{\1}", title)
    return title


TITLE = extract_title()

GITHUB_INLINE_MATH = re.compile(r"\$`([^`\n]+?)`\$")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
FENCE_RE = re.compile(
    r"^```([^\n]*)\n(.*?)^```"
    r"(?:[ \t]*\n+\*\*Figure\.\*\*[ \t]+(.+?))?"
    r"[ \t]*(?=\n|$)",
    re.MULTILINE | re.DOTALL,
)
FENCE_CAPTION_RE = re.compile(r"caption=(['\"])(.*?)\1", re.IGNORECASE)
MANUAL_SECTION_NUM = re.compile(r"^(#{1,6})[ \t]+\d+(?:\.\d+)*\.?[ \t]+", re.MULTILINE)
NARRATIVE_MARKER = "# Narrative (from arxiv.md)"
LEAN_MODULE_RE = re.compile(r"^###\s+([A-Za-z0-9_./-]+\.lean)\s*$", re.MULTILINE)
LEAN_PATH_RE = re.compile(
    r"<!--\s*lean:\s*([A-Za-z0-9_./-]+\.lean)(?:#L(\d+)-L(\d+))?\s*-->"
)


def github_math_to_tex(text: str) -> str:
    return GITHUB_INLINE_MATH.sub(r"$\1$", text)


def strip_html_comments(text: str) -> str:
    return HTML_COMMENT.sub("", text)


def strip_manual_section_numbers(text: str) -> str:
    return MANUAL_SECTION_NUM.sub(r"\1 ", text)


def drop_github_nav(text: str) -> str:
    idx = text.find(NARRATIVE_MARKER)
    if idx == -1:
        return text
    return text[idx + len(NARRATIVE_MARKER) :].lstrip("\n")


def escape_latex_caption(text: str) -> str:
    out: list[str] = []
    for ch in text:
        if ch in "&%$#_{}":
            out.append(f"\\{ch}" if ch != "}" else "\\}")
        elif ch == "~":
            out.append(r"\textasciitilde{}")
        elif ch == "^":
            out.append(r"\textasciicircum{}")
        elif ch == "\\":
            out.append(r"\textbackslash{}")
        else:
            out.append(ch)
    return "".join(out)


def github_blob_url(rel: str, first: int | None = None, last: int | None = None) -> str:
    url = f"{GITHUB_URL}/blob/main/{rel}"
    if first is not None and last is not None:
        url += f"\\#L{first}-L{last}"
    return url


def lean_label_tex(
    label: str, github_rel: str | None, first: int, last: int, line_count: int
) -> str:
    if not github_rel:
        return f"\\textcolor{{green!40!black}}{{\\textbf{{{label}}}}}"
    if first == 1 and last == line_count:
        url = github_blob_url(github_rel)
    else:
        url = github_blob_url(github_rel, first, last)
    return f"\\leansourcehref{{{url}}}{{{label}}}"


def normalize_appendix_headings(text: str) -> str:
    text = re.sub(
        r"^#\s+Appendix A: (?:Complete Lean source|Lean module index)\s*$",
        "## Lean module index",
        text,
        flags=re.MULTILINE,
    )
    text = re.sub(
        r"^##\s+`([A-Za-z0-9_./-]+\.lean)`\s*$",
        r"### \1",
        text,
        flags=re.MULTILINE,
    )
    return text


def extract_abstract(text: str) -> tuple[str, str]:
    m = re.search(
        r"^#{2,3}\s+Abstract\s*\n(.*?)(?=^#{1,3}\s+\S)",
        text,
        re.DOTALL | re.MULTILINE,
    )
    if not m:
        return "", text
    abstract_md = m.group(1).strip()
    body = text[: m.start()] + text[m.end() :]
    return abstract_md, body


def write_listing(code: str, listing_name: str) -> tuple[str, int]:
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
    source = sanitize_lean_for_arxiv(code.rstrip("\n"))
    listing_path = LISTINGS_DIR / listing_name
    listing_path.write_text(source + "\n", encoding="utf-8")
    rel_path = listing_path.relative_to(ROOT).as_posix()
    return rel_path, (len(source.splitlines()) if source else 0)


def caption_md_to_latex(caption: str) -> str:
    """Convert a one-line markdown figure caption to LaTeX."""
    parts: list[str] = []
    token = re.compile(r"(\$[^$]+\$|`[^`]+`)")
    for piece in token.split(caption.strip()):
        if piece.startswith("$") and piece.endswith("$") and len(piece) >= 2:
            parts.append(piece)
        elif piece.startswith("`") and piece.endswith("`") and len(piece) >= 2:
            inner = piece[1:-1].replace("_", r"\_")
            parts.append(r"\texttt{" + inner + "}")
        else:
            parts.append(piece.replace("&", r"\&").replace("%", r"\%").replace("#", r"\#"))
    return "".join(parts)


def mermaid_caption(header: str, following: str | None) -> str:
    if following and following.strip():
        return following.strip()
    m = FENCE_CAPTION_RE.search(header)
    return m.group(2).strip() if m else ""


def figure_latex(rel_path: str, caption: str, idx: int) -> str:
    cap = caption_md_to_latex(caption) if caption else f"Diagram {idx + 1}"
    return (
        "\\begin{figure}[htbp]\n"
        "\\centering\n"
        f"\\includegraphics[max width=\\linewidth,"
        f"max totalheight=0.78\\textheight,keepaspectratio]{{{rel_path}}}\n"
        f"\\caption{{{cap}}}\n"
        f"\\label{{fig:{idx:03d}}}\n"
        "\\end{figure}\n"
    )


def lean_block_latex(code: str, listing_name: str, github_rel: str | None = None) -> str:
    rel_path, line_count = write_listing(code, listing_name)
    ranges = chunk_line_ranges(line_count, LISTING_CHUNK_LINES)

    parts: list[str] = []
    for first, last in ranges:
        label = "Lean 4 source"
        if github_rel:
            label += f" \\texttt{{{escape_latex_caption(github_rel)}}}"
        if not (first == 1 and last == line_count):
            label += f" (lines {first}--{last})"
        firstlast = (
            "" if first == 1 and last == line_count else f",firstline={first},lastline={last}"
        )
        parts.append(
            "\\vspace{0.5\\baselineskip}\n"
            f"\\noindent{lean_label_tex(label, github_rel, first, last, line_count)}"
            "\\par\\vspace{0.25\\baselineskip}\n"
            f"\\lstinputlisting[style=leanbox{firstlast}]{{{rel_path}}}\n"
            "\\vspace{0.5\\baselineskip}\n\n"
        )
    return "".join(parts)


def extract_lean_titles(text: str) -> dict[str, str]:
    """Map LEANINCLUDE000 → github-relative path (optionally with #La-Lb)."""
    titles: dict[str, str] = {}
    lean_starts = [m.start() for m in re.finditer(r"^```lean\s*$", text, re.MULTILINE)]
    for idx, pos in enumerate(lean_starts):
        module = None
        for line in reversed(text[:pos].rstrip("\n").splitlines()[-8:]):
            stripped = line.strip()
            path_m = LEAN_PATH_RE.match(stripped)
            if path_m:
                rel = path_m.group(1)
                a, b = path_m.group(2), path_m.group(3)
                module = f"{rel}#L{a}-L{b}" if a and b else rel
                break
            heading_m = re.match(r"^###\s+([A-Za-z0-9_./-]+\.lean)", stripped)
            if heading_m:
                module = heading_m.group(1)
                break
        titles[f"LEANINCLUDE{idx:05d}"] = module or f"module-{idx + 1}"
    return titles


def replace_fences(
    text: str, lean_titles: dict[str, str] | None = None
) -> tuple[str, dict[str, str]]:
    lean_titles = lean_titles if lean_titles is not None else extract_lean_titles(text)
    placeholders: dict[str, str] = {}
    lean_idx = 0
    other_idx = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal lean_idx, other_idx
        header = match.group(1).strip()
        lang = header.split()[0].lower() if header else ""
        body = match.group(2)
        following_caption = match.group(3)
        if lang == "lean":
            key = f"LEANINCLUDE{lean_idx:05d}"
            module = lean_titles.get(key, f"module-{lean_idx}")
            lean_idx += 1
            github_rel = None
            range_suffix = ""
            if module.endswith(".lean") or "#L" in module:
                if "#L" in module:
                    github_rel, range_suffix = module.split("#L", 1)
                    range_suffix = "L" + range_suffix
                else:
                    github_rel = module
            safe_name = (github_rel or module).replace("/", "-")
            if range_suffix:
                safe_name = safe_name.removesuffix(".lean") + f"-{range_suffix}.lean"
            if not safe_name.endswith(".lean"):
                safe_name += ".lean"
            # uniquify in case of collisions
            safe_name = f"{lean_idx:04d}-{safe_name}"
            placeholders[key] = lean_block_latex(body, safe_name, github_rel)
            return f"\n\n{key}\n\n"
        if lang == "math":
            key = f"MATHINCLUDE{other_idx:03d}"
            other_idx += 1
            placeholders[key] = f"\\[\n{body.strip()}\n\\]\n"
            return f"\n\n{key}\n\n"
        if lang == "mermaid":
            key = f"FIGINCLUDE{other_idx:03d}"
            rel_path = render_mermaid(body, other_idx)
            caption = mermaid_caption(header, following_caption)
            placeholders[key] = figure_latex(rel_path, caption, other_idx)
            other_idx += 1
            return f"\n\n{key}\n\n"
        key = f"CODEINCLUDE{other_idx:03d}"
        rel_path, _ = write_listing(body, f"snippet-{other_idx:03d}.txt")
        other_idx += 1
        placeholders[key] = f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
        return f"\n\n{key}\n\n"

    converted = FENCE_RE.sub(repl, text)
    return converted, placeholders


def pandoc_to_latex(markdown: str, shift: bool = True) -> str:
    cmd = [
        "pandoc",
        "-f",
        "markdown+tex_math_dollars+raw_tex+smart",
        "-t",
        "latex",
        "--wrap=none",
    ]
    if shift:
        cmd += ["--shift-heading-level-by=-1"]
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def inject_placeholders(latex: str, placeholders: dict[str, str]) -> str:
    out = latex
    for key, value in placeholders.items():
        patterns = [
            key,
            f"\\emph{{{key}}}",
            f"\\text{{{key}}}",
            f"\\passthrough{{\\lstinline!{key}!}}",
        ]
        for pat in patterns:
            if pat in out:
                out = out.replace(pat, value)
                break
        else:
            out = out.replace(key, value)
    return out


def break_texttt_paths(latex: str) -> str:
    """Allow line breaks after `/` and `_` in \\texttt paths and identifiers."""

    def fix(match: re.Match[str]) -> str:
        inner = match.group(1)
        inner = inner.replace("/", "/\\allowbreak{}")
        inner = inner.replace(r"\_", r"\_\allowbreak{}")
        inner = re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", inner)
        inner = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", r"\\allowbreak{}", inner)
        inner = inner.replace(".lean", ".\\allowbreak{}lean")
        inner = re.sub(r"\.(?=[A-Za-z])", r".\\allowbreak{}", inner)
        return "\\texttt{" + inner + "}"

    return re.sub(r"\\texttt\{([^{}]*)\}", fix, latex)


def cleanup_pandoc_latex(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n?", "", latex)
    latex = break_texttt_paths(latex)
    for cmd in ("section", "subsection", "subsubsection", "paragraph"):
        latex = re.sub(
            rf"(\\{cmd}\{{)\d+(?:\.\d+)*\.?\s+",
            r"\1",
            latex,
        )
    latex = re.sub(
        r"\\section\{Appendix A\. Lean source index\}",
        "",
        latex,
    )
    latex = re.sub(
        r"\\section\{Appendix A: (?:Complete Lean source|Lean module index)\}",
        r"\\section{Lean module index}",
        latex,
    )
    latex = re.sub(
        r"\\section\{Appendix A\. Lean module index\}",
        r"\\section{Lean module index}",
        latex,
    )
    latex = re.sub(r"\n{3,}", "\n\n", latex)
    return latex


def insert_front_matter_lists(latex: str) -> str:
    """Table of contents and list of figures after CMU front matter (unnumbered)."""
    block = (
        "{\\pagestyle{empty}\n"
        "\\tableofcontents\n"
        "\\clearpage\n"
        "\\listoffigures\n"
        "\\clearpage\n"
        "}\n"
        "\\pagestyle{plain}\n\n"
    )
    return block + latex


REFERENCES_ITEMIZE = re.compile(
    r"(\\hypertarget\{references\}\{%\n\\section\{References\}\\label\{references\}\}\s*\n\n)"
    r"\\begin\{itemize\}\s*\n(.*?)\n\\end\{itemize\}",
    re.DOTALL,
)
REFERENCE_KEY = re.compile(r"\{\[\}(?P<key>[A-Za-z0-9]+)\{]\}")


def format_references_cmu(latex: str) -> str:
    """CMU SCS reports use a numbered thebibliography, not an itemize list."""

    def itemize_to_bib(header: str, items: str) -> str:
        bibitems: list[str] = []
        for i, chunk in enumerate(re.split(r"(?=\\item\s)", items), start=1):
            chunk = chunk.strip()
            if not chunk.startswith("\\item"):
                continue
            key_m = REFERENCE_KEY.search(chunk)
            if key_m:
                key = key_m.group("key")
                body = chunk[key_m.end() :].strip()
            else:
                key = f"R{i}"
                body = re.sub(r"^\\item\s*", "", chunk).strip()
            if body.startswith("}"):
                body = body[1:].strip()
            body = re.sub(r"\s+\n", " ", body)
            bibitems.append(f"\\bibitem{{{key}}} {body}")
        if not bibitems:
            raise RuntimeError("References section itemize was empty or not parseable")
        joined = "\n\n".join(bibitems)
        return f"{header}\\begin{{thebibliography}}{{99}}\n{joined}\n\\end{{thebibliography}}\n"

    updated, count = REFERENCES_ITEMIZE.subn(
        lambda m: itemize_to_bib(m.group(1), m.group(2)), latex
    )
    if count == 1:
        return updated
    plain = re.compile(
        r"(\\section\{References\}(?:\\label\{references\})?\s*\n\n)"
        r"\\begin\{itemize\}\s*\n(.*?)\n\\end\{itemize\}",
        re.DOTALL,
    )
    updated, count = plain.subn(lambda m: itemize_to_bib(m.group(1), m.group(2)), latex)
    if count != 1:
        raise RuntimeError("expected exactly one References itemize block in LaTeX output")
    return updated


def insert_appendix_command(latex: str) -> str:
    marker = r"\section{Lean module index}"
    if marker not in latex:
        raise RuntimeError(f"missing {marker!r} in LaTeX output")
    return latex.replace(marker, r"\appendix" + "\n" + marker, 1)


def cleanup_abstract_latex(latex: str) -> str:
    """Keep the abstract pdfLaTeX/arXiv-safe: ASCII plus standard LaTeX escapes.

    CMU ``\\abstract{...}`` is not ``\\long``, so blank lines / ``\\par`` are
    forbidden inside the argument; flatten to a single paragraph.
    """
    latex = latex.replace("\\pandocbounded{", "{")
    latex = latex.replace("\\textbf{{[}", "\\textbf{[")
    latex = latex.replace("\\texttt{{[}", "\\texttt{[")
    latex = latex.replace("{]}}", "]}")
    latex = re.sub(r"\\begin\{center\}\\rule\{.*?\}\\end\{center\}\s*", "", latex, flags=re.DOTALL)
    latex = re.sub(r"\n\s*\n+", " ", latex)
    latex = re.sub(r"[ \t]*\n[ \t]*", " ", latex)
    latex = re.sub(r"\s+", " ", latex).strip()
    return latex


def build_title_page(abstract_latex: str) -> str:
    return textwrap.dedent(
        f"""
        \\title{{{TITLE}}}

        \\author{{
          Lars Warren Ericson
        }}
        \\disclaimer{{Independent researcher, d/b/a {COMPANY}
          (\\texttt{{{EMAIL}}}; ORCID {ORCID}).}}

        \\date{{{REPORT_DATE}}}
        \\trnumber{{{REPORT_NUMBER}}}
        \\keywords{{Lean 4; formal verification; quantum lambda calculus; linear types;
          CP-presheaf semantics; OpenQASM; quantum relations; quantum CPO}}
        \\abstract{{
        {abstract_latex.strip()}
        }}
        \\hypersetup{{
          pdftitle={{{TITLE}}},
          pdfauthor={{Lars Warren Ericson}},
          pdfsubject={{Carnegie Mellon University School of Computer Science Technical Report {REPORT_NUMBER}}},
          pdfkeywords={{Lean 4, formal verification, quantum lambda calculus, OpenQASM}}
        }}

        \\begin{{document}}

        \\maketitle
        """
    ).strip()


def main() -> int:
    if not SRC.is_file():
        print(f"error: missing {SRC}; run scripts/generate_arxiv_with_code.sh first", file=sys.stderr)
        return 1
    if not PREAMBLE.is_file():
        print(f"error: missing {PREAMBLE}", file=sys.stderr)
        return 1

    for d in (LISTINGS_DIR, FIGURES_DIR):
        if d.exists():
            for path in d.iterdir():
                if path.is_file():
                    path.unlink()
        d.mkdir(parents=True, exist_ok=True)

    raw = SRC.read_text(encoding="utf-8")
    body = drop_github_nav(raw)
    body = inject_model_cards(body)
    # Capture Lean path headers before HTML comments are stripped.
    lean_titles = extract_lean_titles(body)
    body = strip_html_comments(body)
    body = normalize_appendix_headings(body)
    abstract_md, body = extract_abstract(body)
    body = strip_manual_section_numbers(body)
    body = github_math_to_tex(body)
    body, placeholders = replace_fences(body, lean_titles)

    latex_body = pandoc_to_latex(body, shift=True)
    latex_body = inject_placeholders(latex_body, placeholders)
    latex_body = cleanup_pandoc_latex(latex_body)
    latex_body = format_references_cmu(latex_body)
    latex_body = insert_front_matter_lists(latex_body)
    latex_body = insert_appendix_command(latex_body)

    abstract_latex = pandoc_to_latex(github_math_to_tex(abstract_md), shift=False) if abstract_md else ""
    abstract_latex = cleanup_abstract_latex(abstract_latex)

    preamble = PREAMBLE.read_text(encoding="utf-8")
    title_page = build_title_page(abstract_latex)
    document = preamble + "\n\n" + title_page + "\n\n" + latex_body + "\n\n\\end{document}\n"
    OUT.write_text(document, encoding="utf-8")
    n_listings = sum(1 for p in LISTINGS_DIR.iterdir() if p.is_file())
    n_figures = sum(1 for p in FIGURES_DIR.glob("*.png"))
    print(
        f"wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size:,} bytes, "
        f"{n_listings} listings, {n_figures} mermaid figures)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
