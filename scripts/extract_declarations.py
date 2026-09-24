#!/usr/bin/env python3
"""Extract top-level Lean declarations from the checked QLambda surface.

Writes build/declarations.jsonl with kind, name, file, line range, docstring,
signature line, and paper section id.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "build" / "declarations.jsonl"

DECL_KINDS = (
    "structure",
    "class",
    "inductive",
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "example",
)

# Leading attributes / modifiers, then kind, then name (or blank for anonymous example).
DECL_START = re.compile(
    r"^(?P<indent>)"
    r"(?:(?P<attrs>(?:@\[[^\]]*\]\s*)+))?"
    r"(?:(?:noncomputable|protected|private|partial|unsafe|opaque|local)\s+)*"
    r"(?P<kind>" + "|".join(DECL_KINDS) + r")"
    r"(?:\s+(?P<name>[^\s(:{]+))?",
    re.MULTILINE,
)

DOC_BLOCK = re.compile(r"/-[-!]?.*?-/", re.DOTALL)
NAMESPACE_OPEN = re.compile(r"^(namespace|section)\s+(\S+)\s*$")
NAMESPACE_CLOSE = re.compile(r"^(end)(?:\s+(\S+))?\s*$")
IMPORT_LINE = re.compile(r"^import\s+")


def lean_sources() -> list[str]:
    qlambda = sorted(
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "QLambda").rglob("*.lean")
    )
    return ["QLambda.lean"] + qlambda + ["Challenge.lean", "Solution.lean"]


def section_for(path: str) -> str:
    """Map a Lean path to a paper section id used for inline blueprints."""
    if path in ("Challenge.lean", "Solution.lean"):
        return "palomar"
    if path == "QLambda.lean":
        return "intro"
    if path.startswith("QLambda/Domain/"):
        return "sec4"
    if path.startswith("QLambda/Composer/"):
        return "sec8"
    if path.startswith("QLambda/Compiler/") or path.startswith("QLambda/HardwareChannel/"):
        return "sec6"
    if path.startswith("QLambda/CQ/") or path.startswith("QLambda/Source/"):
        return "sec7"
    if path.startswith("QLambda/Linear/"):
        stem = Path(path).name.removesuffix(".lean")
        if "Quote" in stem or stem.startswith("Quotation"):
            return "sec7"
        if stem.startswith("Fragment") or stem in {
            "SemanticFragment",
            "PresheafFragmentModel",
            "Denotation",
            "DenotationInstances",
            "TypeInterpretation",
        }:
            return "sec5"
        if stem in {"Circuit", "Compilation", "Elaboration", "StageResult", "StagedValue"}:
            return "sec6"
        if stem in {
            "Runtime",
            "RuntimeCore",
            "Config",
            "RegFile",
            "PrimitiveSuperoperator",
        } or stem.startswith("Runtime"):
            return "sec3"
        # Syntax, Typing, Context, Operational, Metatheory, Substitution, Examples, …
        return "sec2"
    # Root QLambda/*.lean (densities, Kraus, instruments, …)
    if path.startswith("QLambda/"):
        name = Path(path).name
        if name.startswith(("Quantum", "Kraus", "Normalized", "SubNormalized", "Finite")):
            return "sec3"
        return "sec9"
    return "sec9"


def strip_block_comments_keep_docs(text: str) -> tuple[str, list[tuple[int, int, str]]]:
    """Return text with ordinary /- -/ copyright blocks blanked, keeping /-- docs.

    Also returns list of (start_char, end_char, docstring) for /-- … -/ immediately
    usable when locating decls.
    """
    docs: list[tuple[int, int, str]] = []
    out = list(text)
    for m in DOC_BLOCK.finditer(text):
        block = m.group(0)
        if block.startswith("/--") or block.startswith("/-!"):
            body = block[3:]
            if body.endswith("-/"):
                body = body[:-2]
            docs.append((m.start(), m.end(), body.strip()))
            continue
        # Blank non-doc comments so they do not look like code.
        for i in range(m.start(), m.end()):
            out[i] = "\n" if text[i] == "\n" else " "
    return "".join(out), docs


def docstring_before(docs: list[tuple[int, int, str]], pos: int, text: str) -> str:
    """Find the docstring whose end is immediately before `pos` (whitespace only)."""
    best = ""
    best_end = -1
    for start, end, body in docs:
        if end > pos:
            continue
        between = text[end:pos]
        if between.strip() == "" and end >= best_end:
            best = body
            best_end = end
    return best


def update_namespaces(stack: list[str], line: str) -> None:
    m = NAMESPACE_OPEN.match(line)
    if m:
        stack.append(m.group(2))
        return
    m = NAMESPACE_CLOSE.match(line)
    if m and stack:
        stack.pop()


def fqn(stack: list[str], name: str | None, kind: str) -> str:
    if not name or name in ("{", "where"):
        base = f"_anon_{kind}"
    else:
        base = name
    if not stack:
        return base
    return ".".join(stack + [base])


def find_decl_end(lines: list[str], start_idx: int) -> int:
    """Inclusive end line index for a declaration starting at start_idx (0-based)."""
    n = len(lines)
    i = start_idx + 1
    while i < n:
        line = lines[i]
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            i += 1
            continue
        # Nested doc comment start at col 0 is still part of file, not next decl.
        if line.startswith("/-"):
            i += 1
            continue
        # Next top-level decl or namespace/section/end/import/#command
        if not line.startswith((" ", "\t")):
            if DECL_START.match(line) or NAMESPACE_OPEN.match(line) or NAMESPACE_CLOSE.match(line):
                return i - 1
            if IMPORT_LINE.match(line) or line.startswith("#") or line.startswith("open "):
                return i - 1
            if line.startswith("variable ") or line.startswith("universe "):
                return i - 1
            if line.startswith("set_option ") or line.startswith("attribute "):
                return i - 1
        i += 1
    return n - 1


def extract_file(rel: str) -> list[dict]:
    path = ROOT / rel
    text = path.read_text(encoding="utf-8")
    _, docs = strip_block_comments_keep_docs(text)
    # Use original text for line numbers / signatures; only use docs for prose.
    lines = text.splitlines()
    # Char offsets for docstring matching
    offsets = [0]
    for ln in lines:
        offsets.append(offsets[-1] + len(ln) + 1)

    stack: list[str] = []
    decls: list[dict] = []
    i = 0
    anon_i = 0
    while i < len(lines):
        line = lines[i]
        update_namespaces(stack, line.strip())
        # Attribute lines may precede the decl; scan a small window.
        window = "\n".join(lines[i : min(i + 6, len(lines))])
        # Only match if this line itself starts a decl (or is @ then decl soon).
        m = DECL_START.match(line)
        if not m:
            # Handle `@[simp]\ntheorem ...` where current line is only attributes.
            if line.strip().startswith("@[") and i + 1 < len(lines):
                j = i + 1
                while j < len(lines) and (
                    lines[j].strip().startswith("@[")
                    or lines[j].strip().startswith("noncomputable")
                    or lines[j].strip() == ""
                ):
                    j += 1
                if j < len(lines):
                    m2 = DECL_START.match(lines[j])
                    if m2:
                        i = j
                        line = lines[j]
                        m = m2
            if not m:
                i += 1
                continue

        kind = m.group("kind")
        name = m.group("name")
        if not name or name in ("{", "where", ":"):
            anon_i += 1
            name = f"example_{anon_i}" if kind == "example" else f"anon_{kind}_{anon_i}"

        end_idx = find_decl_end(lines, i)
        start_line = i + 1
        end_line = end_idx + 1
        char_pos = offsets[i]
        doc = docstring_before(docs, char_pos, text)
        # Signature: first non-empty lines until := or where or inductive body
        sig_lines: list[str] = []
        for k in range(i, min(end_idx + 1, i + 12)):
            sig_lines.append(lines[k].rstrip())
            if ":=" in lines[k] or lines[k].rstrip().endswith(" where") or (
                k > i and lines[k].startswith("  |")
            ):
                break
        signature = "\n".join(sig_lines).strip()
        decls.append(
            {
                "kind": kind,
                "name": name,
                "fqn": fqn(list(stack), name, kind),
                "file": rel,
                "start_line": start_line,
                "end_line": end_line,
                "docstring": doc,
                "signature": signature,
                "section": section_for(rel),
                "is_example": kind == "example"
                or "Fixture" in rel
                or "/Examples.lean" in rel
                or rel.endswith("Fixtures.lean")
                or "_test" in name.lower()
                or name.lower().startswith("bell")
                or "measured_control" in name.lower(),
            }
        )
        i = end_idx + 1
    return decls


def main() -> None:
    OUT.parent.mkdir(parents=True, exist_ok=True)
    all_decls: list[dict] = []
    for rel in lean_sources():
        if not (ROOT / rel).is_file():
            print(f"warning: missing {rel}", file=sys.stderr)
            continue
        all_decls.extend(extract_file(rel))

    with OUT.open("w", encoding="utf-8") as f:
        for d in all_decls:
            f.write(json.dumps(d, ensure_ascii=False) + "\n")

    by_kind: dict[str, int] = {}
    by_sec: dict[str, int] = {}
    for d in all_decls:
        by_kind[d["kind"]] = by_kind.get(d["kind"], 0) + 1
        by_sec[d["section"]] = by_sec.get(d["section"], 0) + 1
    print(f"wrote {OUT} ({len(all_decls)} declarations)")
    print("by kind:", dict(sorted(by_kind.items(), key=lambda kv: -kv[1])))
    print("by section:", dict(sorted(by_sec.items())))


if __name__ == "__main__":
    main()
