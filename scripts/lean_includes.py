#!/usr/bin/env python3
"""Expand <!-- lean: path --> and <!-- lean: path#La-Lb --> markers to lean fences.

Fail-closed if the path or line range is missing/invalid.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# path optionally followed by #Lstart-Lend
LEAN_INCLUDE = re.compile(
    r"<!--\s*lean:\s*([^\s#]+?)(?:#L(\d+)-L(\d+))?\s*-->"
    r"(?:\s*```lean\n.*?^```)*",
    re.MULTILINE | re.DOTALL,
)


def expand_lean_includes(text: str, root: Path = ROOT) -> str:
    def repl(match: re.Match[str]) -> str:
        rel = match.group(1)
        start_s, end_s = match.group(2), match.group(3)
        path = root / rel
        if not path.is_file():
            raise FileNotFoundError(f"lean include missing: {rel}")
        lines = path.read_text(encoding="utf-8").splitlines()
        if start_s is None:
            code = "\n".join(lines).rstrip()
            header = f"<!-- lean: {rel} -->"
        else:
            a, b = int(start_s), int(end_s)
            if a < 1 or b < a or b > len(lines):
                raise ValueError(
                    f"lean include range out of bounds: {rel}#L{a}-L{b} "
                    f"(file has {len(lines)} lines)"
                )
            code = "\n".join(lines[a - 1 : b]).rstrip()
            header = f"<!-- lean: {rel}#L{a}-L{b} -->"
        return f"{header}\n\n```lean\n{code}\n```\n"

    return LEAN_INCLUDE.sub(repl, text)


if __name__ == "__main__":
    import sys

    src = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "arxiv.md"
    print(expand_lean_includes(src.read_text(encoding="utf-8"))[:500])
