#!/usr/bin/env python3
"""Per-module English roles for the Lean module index appendix.

Roles are derived from (in order):
  1. the module `/-!` docstring headline,
  2. the English blueprint subsection titles for declarations in that file,
  3. a humanized path stem — never a coarse directory-wide label.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))

from generate_blueprint_cards import cap, de_code_text, gloss_backticks, is_codey  # noqa: E402

MODULE_DOC = re.compile(r"/-!\s*(.*?)\n-/", re.DOTALL)
HEADING = re.compile(r"^#\s+(.+)$", re.MULTILINE)
CARD_TITLE = re.compile(r"^####\s+(.+)$", re.MULTILINE)


def module_doc_headline(rel: str) -> str | None:
    path = ROOT / rel
    if not path.is_file():
        return None
    text = path.read_text(encoding="utf-8")
    m = MODULE_DOC.search(text)
    if not m:
        return None
    body = m.group(1).strip()
    hm = HEADING.search(body)
    if hm:
        return mathematical(re.sub(r"\s+", " ", hm.group(1)).strip().rstrip("."))
    # First non-empty paragraph
    for para in re.split(r"\n\s*\n", body):
        line = re.sub(r"\s+", " ", para).strip()
        if line and not line.startswith("```"):
            # Keep short; truncate long architectural notes.
            if len(line) > 140:
                line = line[:137].rstrip() + "…"
            return mathematical(line.rstrip("."))
    return None


def mathematical(text: str) -> str:
    """Replace Lean identifiers in author prose by their English glosses."""
    out = gloss_backticks(text, None)
    if is_codey(out):
        out = de_code_text(out)
    return cap(re.sub(r"\s+", " ", out).strip())


def role_phrase(title: str) -> str:
    """Card heading → Role-column phrase (drop boilerplate prefixes)."""
    t = re.sub(r"^Definition of (?:the )?", "", title)
    t = re.sub(r"^The (?:structure|interface|inductive definition) of ", "", t)
    return cap(t)


def humanize_stem(rel: str) -> str:
    stem = Path(rel).stem
    # Strip common Lean instance prefixes.
    stem = re.sub(r"^inst", "", stem)
    stem = re.sub(r"_+", " ", stem)
    stem = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", stem)
    stem = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", " ", stem)
    return stem.strip()


def blueprint_titles_for(rel: str, cards_dir: Path) -> list[str]:
    """Collect English #### titles whose lean markers cite this file."""
    if not cards_dir.is_dir():
        return []
    titles: list[str] = []
    marker = f"<!-- lean: {rel}#"
    for path in sorted(cards_dir.glob("*.md")):
        text = path.read_text(encoding="utf-8")
        # Split into cards roughly by #### headings
        parts = re.split(r"(?=^#### )", text, flags=re.MULTILINE)
        for part in parts:
            if marker not in part:
                continue
            tm = CARD_TITLE.match(part)
            if tm:
                title = role_phrase(tm.group(1).strip())
                if is_codey(title):
                    continue
                if title and not title.startswith("Module ") and title not in titles:
                    titles.append(title)
    return titles


def summarize_titles(titles: list[str], limit: int = 3) -> str | None:
    if not titles:
        return None

    def rank(t: str) -> tuple[int, int]:
        low = t.lower()
        # Prefer substantive definitional / named results over anon noise.
        if "anonymous" in low or low.startswith("anon"):
            return (5, -len(t))
        if low in {"definition of top", "definition of bot", "definition of id"}:
            return (4, -len(t))
        if len(t) > 110:
            return (3, len(t))
        if re.search(r"\b(?:is|are|equals|preserves|holds|determines|splits|coincide)\b", low):
            return (0, len(t))  # statements of results read best
        if low.startswith(("allocation", "theorem", "lemma", "instance for")):
            return (1, -len(t))
        if low.startswith("example:"):
            return (3, -len(t))
        return (2, -len(t))

    ranked = sorted(titles, key=rank)
    picked = [t for t in ranked if "anonymous" not in t.lower()][:limit]
    if not picked:
        picked = ranked[:limit]
    if len(titles) <= limit:
        return "; ".join(picked)
    return "; ".join(picked) + f"; … ({len(titles)} declarations)"


def file_role(rel: str, cards_dir: Path | None = None) -> str:
    """English one-liner for the module index Role column."""
    if rel == "QLambda.lean":
        return "Root import graph for the QLambda library"
    if rel == "Challenge.lean":
        return "Palomar challenge statements"
    if rel == "Solution.lean":
        return "Palomar compared solutions"

    doc = module_doc_headline(rel)
    cards = cards_dir if cards_dir is not None else ROOT / "build" / "blueprint_cards"
    titles = blueprint_titles_for(rel, cards)
    summary = summarize_titles(titles)

    if doc and summary and re.match(r"^(?:Instances?|Instance)\b", doc):
        return summary
    if doc and summary:
        # Tie the module headline to representative blueprint subsection titles.
        if doc.lower() not in summary.lower() and summary.lower() not in doc.lower():
            # Keep the Role cell readable in the longtable.
            combined = f"{doc} — {summary}"
            if len(combined) > 220:
                combined = combined[:217].rstrip() + "…"
            return combined
        return doc
    if doc:
        return doc
    if summary:
        return summary

    stem = de_code_text(humanize_stem(rel))
    if rel.startswith("QLambda/Domain/"):
        return f"Domain: {stem}"
    if rel.startswith("QLambda/Linear/"):
        return f"Linear language: {stem}"
    if rel.startswith("QLambda/Composer/"):
        return f"Composer / OpenQASM: {stem}"
    if rel.startswith("QLambda/CQ/"):
        return f"Classical–quantum semantics: {stem}"
    if rel.startswith("QLambda/Compiler/"):
        return f"Compiler: {stem}"
    if rel.startswith("QLambda/HardwareChannel/"):
        return f"Hardware channel: {stem}"
    if rel.startswith("QLambda/Source/"):
        return f"Source utilities: {stem}"
    return stem or "QLambda module"


if __name__ == "__main__":
    import sys

    sample = sys.argv[1:] or [
        "QLambda/Domain/QuantumRel.lean",
        "QLambda/Linear/PrimitiveSuperoperator.lean",
        "QLambda/Composer/Fixtures.lean",
    ]
    for rel in sample:
        print(rel, "=>", file_role(rel))
