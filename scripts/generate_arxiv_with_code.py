#!/usr/bin/env python3
"""Append Lean module index to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GITHUB = "https://github.com/catskillsresearch/qlambda"


def lean_sources() -> list[str]:
    """Complete checked source surface, excluding build caches."""
    qlambda = sorted(
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "QLambda").rglob("*.lean")
    )
    return ["QLambda.lean"] + qlambda + ["Challenge.lean", "Solution.lean"]


FILES = lean_sources()


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


def main() -> None:
    missing = [f for f in FILES if not (ROOT / f).is_file()]
    if missing:
        raise SystemExit(f"missing Lean files: {missing[:5]}{'...' if len(missing) > 5 else ''} ({len(missing)} total)")

    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = narrative_body(arxiv)

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
        f"*Generated {date.today().isoformat()} from `arxiv.md` and the module list "
        "in `scripts/generate_arxiv_with_code.py`.*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "This file appends **Appendix A: Lean module index** with GitHub links "
        "(no inlined full source).\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **Narrative** | Full `arxiv.md` body with inline Lean gists |\n")
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
    out.write_text("".join(parts))
    print(f"wrote {out} ({total_lines} Lean lines indexed across {len(FILES)} files)")


if __name__ == "__main__":
    main()
