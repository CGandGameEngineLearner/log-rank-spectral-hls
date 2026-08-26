# Sharp sparse Log-Rank on Johnson columns

Reviewer and arXiv repository for the manuscript
**Logarithmic Communication for Low-Degree Slices and Product Domains with
Spectral--Lattice Stability**.

## Headline results

For a uniform random (B\in\binom{[n]}k), every nontrivial set (A) and
integer (a) satisfy the globally sharp bound

\[
\Pr[|A\cap B|\notin\{a,a+1\}]
\ge \frac25\left(\frac{\min\{k,n-k\}}n\right)^2.
\]

Equality occurs only at

\[
(n,k,|A|,a)=(6,3,3,1).
\]

For the sparse Johnson column families constructed in the paper, with actual
restricted real rank (r),

\[
D(M)\le\lceil\log_2(r+1)\rceil+1,
\qquad
\operatorname{rect}(M)\ge\frac1{4(r+1)}.
\]

On a β-balanced layer, the anchor-free random family remains valid after
adversarial deletion of a β²/10-fraction of all sampled columns. The paper
also gives a deterministic covariance-gap theorem, broad `2`-design
consequences, and an explicit information-theoretically minimal
Sylvester--Hadamard family on (n=2^t-1).

These are restricted-column results. They do **not** prove the general
Log-Rank Conjecture or improve the universal (O(\sqrt r)) bound for every
Boolean matrix.

## Repository layout

- `paper/`: submission LaTeX and bibliography;
- `output/pdf/`: stable compiled manuscript;
- `formal/`: curated 18-module Lean core (reduced from 63 research modules);
- `scripts/`: five deterministic/exhaustive verification programs;
- `docs/REVIEWER_GUIDE.md`: theorem-to-evidence reading map;
- `docs/CLAIMS_AND_LIMITATIONS.md`: precise claim boundary;
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

## Submission gate

The manuscript currently retains the author line `Anonymous draft`. Replace
it with final author metadata before an arXiv or journal submission. The work
has extensive machine checks but has not yet received external peer review or
priority certification.
