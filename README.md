# Sharp two-point escape on Johnson products and sparse columns

Reviewer and arXiv repository for the manuscript
**Sharp Two-Point Escape and Logarithmic Communication for Johnson Products
and Sparse Columns**.

## Headline results

For $2\le k\le n-2$, a uniform random $B\in\binom{[n]}k$, every set
with $2\le|A|\le n-2$, and every integer $a$ satisfy the globally sharp
bound

\[
\Pr[|A\cap B|\notin\{a,a+1\}]
\ge \frac25\left(\frac{\min\{k,n-k\}}n\right)^2.
\]

Equality occurs only at

\[
(n,k,|A|,a)=(6,3,3,1).
\]

For products of interior Johnson layers `2 <= k_i <= n_i-2`, every
nonconstant admissible row is a coordinate function or its complement. The
exact bounds are `D(M) <= ceil(log2(rank(M)+1))+4` and rectangle density at
least `1/(4(d+1))`. At the selector boundary `k_i=1`, arbitrary Boolean
matrices embed; this is the structural boundary of the product theorem.

For the sparse Johnson column families constructed in the paper, with actual
restricted real rank $r$,

\[
D(M)\le\lceil\log_2(r+1)\rceil+1,
\qquad
\operatorname{rect}(M)\ge\frac1{4(r+1)}.
\]

On a β-balanced layer, the anchor-free random family remains valid after
adversarial deletion of a β²/10-fraction of all sampled columns. The paper
also gives a deterministic covariance-gap theorem, broad `2`-design
consequences, and an explicit information-theoretically minimal
Sylvester--Hadamard family on $n=2^t-1$.

These are restricted-column results. They do **not** prove the general
Log-Rank Conjecture or improve the universal $O(\sqrt r)$ bound for every
Boolean matrix.

## Repository layout

- `paper/`: submission LaTeX and bibliography;
- `output/pdf/`: stable compiled manuscript;
- `formal/`: curated 18-module Lean core (reduced from 63 research modules);
- `scripts/`: five deterministic/exhaustive verification programs;
- `docs/REVIEWER_GUIDE.md`: theorem-to-evidence reading map;
- `docs/CLAIMS_AND_LIMITATIONS.md`: precise claim boundary;
- `docs/PRIORITY_AND_PROTOCOL_AUDIT.md`: targeted prior-art and endpoint
  protocol audit;
- `docs/REPRODUCIBILITY.md`: commands and expected outputs;
- `docs/ARXIV_SUBMISSION.md`: release checklist and source-package workflow.

## Quick verification

```bash
make verify-python
make verify-lean
make paper
```

Or run everything:

```bash
make all
```

The Lean build downloads the pinned Mathlib revision on its first standard
`lake` run. See `docs/REPRODUCIBILITY.md` for the cached local build used to
validate this repository.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22120314.svg)](https://doi.org/10.5281/zenodo.22120314)

## Citing this repository

This GitHub repository is the versioned source archive (paper, Lean core,
and verification scripts). Cite the latest archived snapshot via the
concept DOI, which always resolves to the current version:

Li, J. (2026). Sharp Two-Point Escape and Logarithmic Communication for
Johnson Products and Sparse Columns (v1.0.1). Zenodo.
https://doi.org/10.5281/zenodo.22120314

The version DOI for `v1.0.0` is https://doi.org/10.5281/zenodo.22120315.
The scholarly preprint, when posted, should be cited from arXiv (`cs.CC`),
not from this software DOI.

## Submission gate

The manuscript metadata now lists JinWen Li, SouthWest Petroleum University,
and lifesize1@163.com. The work has extensive machine checks but has not yet
received external peer review or priority certification. The repository is
licensed under [CC BY 4.0](LICENSE).
