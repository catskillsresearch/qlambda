#!/usr/bin/env bash
# Build a Zenodo deposit zip: PDF + narrative + Lean sources + license + metadata.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PDF="arxiv.pdf"
OUT_DIR="dist"
STAGE="${OUT_DIR}/zenodo-stage"
ZIP="${OUT_DIR}/qlambda-zenodo.zip"

if [[ "${1:-}" != "--skip-pdf-build" ]]; then
  echo "==> Building PDF (and arXiv zip) via build_arxiv_pdf.sh"
  bash scripts/build_arxiv_pdf.sh
fi

missing=0
for req in "$PDF" arxiv.md LICENSE README.md lean-toolchain lakefile.toml \
    QLambda.lean .zenodo.json CITATION.cff PROVENANCE.md; do
  if [[ ! -e "$req" ]]; then
    echo "error: missing $req" >&2
    missing=1
  fi
done
if [[ ! -d Quantum ]]; then
  echo "error: missing Quantum/" >&2
  missing=1
fi
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -rf "$STAGE"
mkdir -p "$STAGE"

cat > "${STAGE}/README-ZENODO.md" <<'EOF'
# qlambda — Zenodo deposit

Lean 4 / Palomar snapshot of ωQVA and the quantum domain equation
D_∞ ≅ [D_∞ → Q(D_∞)], with a vendored scott1972 foundation.

Repository: https://github.com/catskillsresearch/qlambda

## Rebuild Lean

```bash
lake exe cache get
lake build
```

## Rebuild this deposit

```bash
bash scripts/package_zenodo.sh
bash scripts/package_zenodo.sh --skip-pdf-build
```

Upload `dist/qlambda-zenodo.zip` at https://zenodo.org/deposit/new
EOF

cp -f "$PDF" "${STAGE}/arxiv.pdf"
cp -f arxiv.md LICENSE README.md .zenodo.json CITATION.cff PROVENANCE.md NOTICE \
  formalization.yaml comparator.json "${STAGE}/"
cp -f lean-toolchain lakefile.toml QLambda.lean Challenge.lean Solution.lean \
  QuantumStateSpace.lean "${STAGE}/"
[[ -e lake-manifest.json ]] && cp -f lake-manifest.json "${STAGE}/"
mkdir -p "${STAGE}/Quantum" "${STAGE}/vendor"
find Quantum -type f -name '*.lean' -print0 | while IFS= read -r -d '' f; do
  dest="${STAGE}/${f}"
  mkdir -p "$(dirname "$dest")"
  cp -f "$f" "$dest"
done
cp -R vendor/FROZEN.txt "${STAGE}/vendor/" 2>/dev/null || true

rm -f "$ZIP"
(
  cd "$STAGE"
  zip -r "../qlambda-zenodo.zip" . >/dev/null
)

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Upload $ZIP to Zenodo: https://zenodo.org/deposit/new"
