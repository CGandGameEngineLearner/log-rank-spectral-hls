# Reviewer guide

## Suggested reading order

1. Abstract and introduction: scope and claim boundary.
2. The unisolvent sparse-column transfer subsection.
3. The global sharp hypergeometric two-point theorem and equality case.
4. The anchor-free robust sparse-HLS theorem.
5. The deterministic covariance-gap theorem and the `2`-design/Hadamard
   corollaries.
6. Product-Johnson and low-degree transfer sections as broader applications.
7. Machine-verification section and this repository's evidence map.

## Headline evidence map

| Claim | Paper evidence | Lean core | Computational audit |
|---|---|---|---|
| Global sharp `2/5` escape and unique equality | Six-coordinate all-trace proof | `SharpSixCoordinateGap` | 123,750 certificate parameters; 2,047,045 intervals |
| Short-side and low-density subproofs | Explicit cleared polynomials | `SharpThreeMarkedGap`, `SharpLowDensityGap` | Included in exact audit |
| Unisolvent rank lifting | Sparse transfer proof | `UnisolventRestriction` | Minimal-basis and Booleanity tests |
| Anchor-free affine support | Swap-pair proof | `AffineSupportPairing` | 221,535 forms / 9,241,290 values |
| Deterministic spectral terminal | Covariance variance proof | `DeterministicSpectralSparseHLS` | Hadamard design checks |
| Explicit Hadamard family | Symmetric `2`-design calculation | threshold in `DeterministicSpectralSparseHLS` | six parameters through `t=8` |
| Actual-rank protocol core | rank pooling and factorization | `JuntaRankPooling`, `RankBound` | rank/protocol suites |
| Product-Johnson structure | range and kernel proofs | product/range modules | 2,533,728 row-column checks |

## What is deliberately omitted

The original research workspace contains historical Fourier, affine-section,
rectangle-extraction, and exploratory Lean modules. They are not dependencies
of the headline claims above and are intentionally excluded. The curated core
contains no generated `.olean` files, caches, screenshots, temporary output,
or abandoned proof routes.

## Reviewer commands

```bash
make verify-python
make verify-lean
make paper
```

All programs fail by assertion or nonzero exit status if a certified identity
or count changes.
