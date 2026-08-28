#!/usr/bin/env bash
# Build a Zenodo deposit zip: PDF + narrative + Lean sources + license + metadata.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PDF="arxiv.pdf"
OUT_DIR="dist"
ZIP="${OUT_DIR}/qlambda-zenodo.zip"
STAGE="$(mktemp -d "${TMPDIR:-/tmp}/qlambda-zenodo-stage.XXXXXX")"
TMP_ZIP="${STAGE}.zip"
trap 'rm -rf "$STAGE"; rm -f "$TMP_ZIP"' EXIT

if [[ "${1:-}" != "--skip-pdf-build" ]]; then
  echo "==> Building PDF (and arXiv zip) via build_arxiv_pdf.sh"
  bash scripts/build_arxiv_pdf.sh
fi

missing=0
for req in "$PDF" arxiv.md LICENSE README.md lean-toolchain lakefile.toml \
    QLambda.lean .zenodo.json CITATION.cff PROVENANCE.md NOTICE \
    formalization.yaml comparator.json Challenge.lean Solution.lean \
    THEOREMS.md ZENODO.md vendor/FROZEN.txt \
    vendor/scott1972/Scott1972.lean vendor/scott1972/LICENSE \
    vendor/scott1972/README.md vendor/scott1972/CITATION.cff \
    vendor/scott1972/.zenodo.json vendor/scott1972/lakefile.toml \
    vendor/scott1972/lake-manifest.json vendor/scott1972/lean-toolchain; do
  if [[ ! -e "$req" ]]; then
    echo "error: missing $req" >&2
    missing=1
  fi
done
if [[ ! -d QLambda ]]; then
  echo "error: missing QLambda/" >&2
  missing=1
fi
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"

cat > "${STAGE}/README-ZENODO.md" <<'EOF'
# qlambda — Zenodo deposit

Lean 4 / Palomar snapshot of ωQVA and the quantum domain equation
D_∞ ≅ [D_∞ → Q(D_∞)], with a vendored scott1972 foundation.

Repository: https://github.com/catskillsresearch/qlambda

## Rebuild Lean

```bash
lake exe cache get
lake build
bash scripts/compare_challenge_solution_types.sh
```

## Rebuild the PDF and this deposit

The PDF build additionally requires Python 3, Pandoc, Mermaid CLI (`mmdc`)
with a Chromium-compatible browser, `latexmk`, LuaLaTeX, `zip`, and `unzip`.

```bash
bash scripts/package_zenodo.sh
```

To rebuild only the archive from the included `arxiv.pdf`:

```bash
bash scripts/package_zenodo.sh --skip-pdf-build
```

Upload `dist/qlambda-zenodo.zip` at https://zenodo.org/deposit/new
EOF

cp -f "$PDF" "${STAGE}/arxiv.pdf"
cp -f arxiv.md LICENSE README.md .zenodo.json CITATION.cff PROVENANCE.md NOTICE \
  formalization.yaml comparator.json THEOREMS.md ZENODO.md "${STAGE}/"
cp -f lean-toolchain lakefile.toml QLambda.lean Challenge.lean Solution.lean "${STAGE}/"
[[ -e lake-manifest.json ]] && cp -f lake-manifest.json "${STAGE}/"
mkdir -p "${STAGE}/QLambda" "${STAGE}/scripts" "${STAGE}/vendor/scott1972"
find QLambda -type f -name '*.lean' -print0 | while IFS= read -r -d '' f; do
  dest="${STAGE}/${f}"
  mkdir -p "$(dirname "$dest")"
  cp -f "$f" "$dest"
done
find scripts -maxdepth 1 -type f \
    \( -name '*.sh' -o -name '*.py' -o -name '*.json' -o -name '*.tex' \) \
    -exec cp -f {} "${STAGE}/scripts/" \;
find vendor/scott1972 -path '*/.lake' -prune -o \
    -type f -name '*.lean' -print0 | while IFS= read -r -d '' f; do
  dest="${STAGE}/${f}"
  mkdir -p "$(dirname "$dest")"
  cp -f "$f" "$dest"
done
cp -f vendor/FROZEN.txt "${STAGE}/vendor/"
cp -f vendor/scott1972/LICENSE vendor/scott1972/README.md \
  vendor/scott1972/CITATION.cff vendor/scott1972/.zenodo.json \
  vendor/scott1972/ZENODO.md vendor/scott1972/lakefile.toml \
  vendor/scott1972/lake-manifest.json vendor/scott1972/lean-toolchain \
  "${STAGE}/vendor/scott1972/"

(
  cd "$STAGE"
  zip -r "$TMP_ZIP" . >/dev/null
)
mv -f "$TMP_ZIP" "$ZIP"

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Upload $ZIP to Zenodo: https://zenodo.org/deposit/new"
