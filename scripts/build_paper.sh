#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="$(mktemp -d /tmp/log-rank-paper-XXXXXX)"
STAGE="$ROOT/output/arxiv/staging"

cp "$ROOT/paper/main.tex" "$ROOT/paper/references.bib" "$BUILD/"
cd "$BUILD"
pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null
bibtex main >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null

mkdir -p "$ROOT/output/pdf" "$ROOT/output/arxiv"
cp main.pdf "$ROOT/output/pdf/spectral_lattice_logrank.pdf"
cp main.bbl "$ROOT/paper/main.bbl"

rm -rf "$STAGE"
mkdir -p "$STAGE"
cp "$ROOT/paper/main.tex" "$ROOT/paper/references.bib" \
  "$ROOT/paper/main.bbl" "$STAGE/"
cp "$ROOT/docs/ARXIV_README.txt" "$STAGE/README"
tar -C "$STAGE" -czf "$ROOT/output/arxiv/log-rank-spectral-hls-arxiv.tar.gz" .

echo "PDF: $ROOT/output/pdf/spectral_lattice_logrank.pdf"
echo "arXiv source: $ROOT/output/arxiv/log-rank-spectral-hls-arxiv.tar.gz"
