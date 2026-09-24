#!/usr/bin/env python3
"""Append Lean module index to arxiv.md → arxiv_with_code.md (build artifact).

Also expands:
  <!-- blueprints:SECTION -->  → Mathlib dep figure + declaration cards
  <!-- lean: path[#La-Lb] -->   → fenced Lean excerpts (fail-closed)
"""

from __future__ import annotations

import re
import subprocess
import sys
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from lean_includes import expand_lean_includes

GITHUB = "https://github.com/catskillsresearch/qlambda"
BLUEPRINT_RE = re.compile(r"<!--\s*blueprints:\s*([A-Za-z0-9_-]+)\s*-->")
CARDS = ROOT / "build" / "blueprint_cards"
DEPS = ROOT / "build" / "section_dep_figures"


def lean_sources() -> list[str]:
    qlambda = sorted(
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "QLambda").rglob("*.lean")
    )
    return ["QLambda.lean"] + qlambda + ["Challenge.lean", "Solution.lean"]


FILES = lean_sources()


def ensure_blueprint_artifacts() -> None:
    """Regenerate declaration catalog, English cards, and Mathlib dep figures."""
    steps = [
        ["python3", str(SCRIPTS / "extract_declarations.py")],
        ["python3", str(SCRIPTS / "generate_blueprint_cards.py")],
        ["python3", str(SCRIPTS / "insert_section_dep_figures.py")],
    ]
    for cmd in steps:
        proc = subprocess.run(cmd, cwd=ROOT, check=False)
        if proc.returncode != 0:
            raise SystemExit(f"blueprint prep failed: {' '.join(cmd)}")


def file_role(path: str) -> str:
    if path == "QLambda.lean":
        return "QLambda root import graph"
    if path == "Challenge.lean":
        return "Palomar challenge statements"
    if path == "Solution.lean":
        return "Palomar compared solutions"
    if path.startswith("QLambda/Domain/"):
        return "Quantum relation, qCPO, and LNL semantics"
    if path.startswith("QLambda/Linear/"):
        return "Typed linear language, runtime, and circuit correspondence"
    if path.startswith("QLambda/Composer/"):
        return "Composer/OpenQASM interchange"
    return "QLambda development"


def github_blob(rel: str) -> str:
    return f"{GITHUB}/blob/main/{rel}"


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# QLambda"
    if first.startswith("# "):
        return first[2:].strip()
    return first.strip()


def narrative_body(arxiv_text: str) -> str:
    body = arxiv_text
    if body.startswith("# "):
        idx = body.find("\n---\n")
        if idx != -1:
            body = body[idx + len("\n---\n") :]
        else:
            body = body[body.find("\n") + 1 :]
    return body.rstrip()


def expand_blueprints(text: str) -> str:
    missing: list[str] = []

    def repl(match: re.Match[str]) -> str:
        sec = match.group(1)
        dep_path = DEPS / f"{sec}.md"
        card_path = CARDS / f"{sec}.md"
        parts: list[str] = []
        if dep_path.is_file():
            parts.append(dep_path.read_text(encoding="utf-8").rstrip() + "\n\n")
        else:
            missing.append(f"dep figure {sec}")
        if card_path.is_file():
            parts.append(card_path.read_text(encoding="utf-8").rstrip() + "\n")
        else:
            missing.append(f"cards {sec}")
        if not parts:
            raise FileNotFoundError(f"no blueprint artifacts for section {sec}")
        return "".join(parts)

    out = BLUEPRINT_RE.sub(repl, text)
    if missing:
        raise SystemExit(f"missing blueprint artifacts: {missing}")
    return out


def coverage_check(text: str) -> None:
    """Fail if any declaration file/range marker is absent from the expanded narrative."""
    decls_path = ROOT / "build" / "declarations.jsonl"
    if not decls_path.is_file():
        raise SystemExit("missing declarations.jsonl")
    import json

    decls = [
        json.loads(line)
        for line in decls_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    absent = []
    for d in decls:
        marker = f"<!-- lean: {d['file']}#L{d['start_line']}-L{d['end_line']} -->"
        if marker not in text:
            absent.append(d["fqn"])
    if absent:
        sample = ", ".join(absent[:8])
        raise SystemExit(
            f"coverage gate: {len(absent)} declarations missing from narrative "
            f"(e.g. {sample})"
        )
    print(f"coverage gate: {len(decls)} declarations present in narrative")


def main() -> None:
    ensure_blueprint_artifacts()

    missing = [f for f in FILES if not (ROOT / f).is_file()]
    if missing:
        raise SystemExit(
            f"missing Lean files: {missing[:5]}"
            f"{'...' if len(missing) > 5 else ''} ({len(missing)} total)"
        )

    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = narrative_body(arxiv)
    body = expand_blueprints(body)
    body = expand_lean_includes(body)
    coverage_check(body)

    project_files = list(FILES)

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — narrative + Lean module index\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`. "
        "This file is stale whenever it is older than `arxiv.md` or any listed `.lean` file.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md`, blueprint cards, "
        "and the module list in `scripts/generate_arxiv_with_code.py`.*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "with inline Mathlib dependency figures and per-declaration English/Lean "
        "blueprints expanded. "
        "This file appends **Appendix A: Lean module index** with GitHub links "
        "(filename index only; blueprints live in the narrative).\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append(
        "| **Narrative** | Full `arxiv.md` body with inline Mathlib deps + Lean blueprints |\n"
    )
    parts.append("| **Appendix A** | Hyperlinked module index |\n\n")
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Lean module index\n\n")
    parts.append(
        f"Checked by `lake build`. Repository: [{GITHUB}]({GITHUB}).\n\n"
    )

    def append_table(title: str, paths: list[str]) -> None:
        parts.append(f"### {title}\n\n")
        parts.append("| Role | File |\n")
        parts.append("| --- | --- |\n")
        for f in paths:
            parts.append(f"| {file_role(f)} | [`{f}`]({github_blob(f)}) |\n")
        parts.append("\n")

    append_table("QLambda project and Palomar", project_files)

    total_lines = sum(len((ROOT / f).read_text().splitlines()) for f in FILES)
    parts.append(
        f"**Total indexed:** {len(FILES)} files, {total_lines} lines of Lean.\n\n"
    )

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(
        f"wrote {out} ({total_lines} Lean lines indexed across {len(FILES)} files)"
    )


if __name__ == "__main__":
    main()
