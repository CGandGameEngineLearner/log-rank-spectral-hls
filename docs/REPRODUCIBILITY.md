# Reproducibility

## Requirements

- Python 3.10 or newer;
- Lean 4.22.0 and Lake;
- Mathlib `v4.22.0` (pinned in `formal/lakefile.toml`);
- `pdflatex`, `bibtex`, and standard AMS LaTeX packages;
- Poppler (`pdfinfo`, `pdftoppm`) for optional PDF inspection.

## Python verification

```bash
make verify-python
```

Expected terminal line:

```text
all Python verification suites: PASS
```

The largest current audits include:

- 2,047,045 adjacent hypergeometric intervals;
- 123,750 six-coordinate certificate parameter pairs;
- 9,241,290 affine support evaluations;
- 2,533,728 product-Johnson row-column checks.

## Lean verification

Portable build:

```bash
cd formal
lake update
lake build
```

The development contains 18 source modules and no project-defined axioms,
`sorry`, or `admit`.

For the WSL validation machine used to prepare this repository, a previously
compiled Mathlib tree was supplied through `LEAN_PATH`; this changes only the
build speed, not the checked source or pinned versions.

## Paper and arXiv source

```bash
make paper
```

Outputs:

- `output/pdf/spectral_lattice_logrank.pdf`;
- `output/arxiv/log-rank-spectral-hls-arxiv.tar.gz`.

The arXiv tarball deliberately contains only `main.tex`, `references.bib`,
`main.bbl`, and a short README. Reviewer code remains in Git rather than in
the TeX upload bundle.
