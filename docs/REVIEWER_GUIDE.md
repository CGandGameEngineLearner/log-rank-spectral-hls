# Reviewer guide

## Suggested reading order

1. Abstract and introduction: scope and claim boundary.
2. Main theorem I: the global sharp interior-hypergeometric `2/5` escape
   theorem.
3. Main theorem II: interior Johnson products and the `k_i=1` selector
   boundary.
4. Main theorem III: unisolvent sparse columns, anchor-free robustness, and
   deterministic spectral/Hadamard columns.
5. Rank-pooled query transfer as an auxiliary consequence.
6. Related work, limitations, and the machine-verification boundary.
7. Appendices for standard sampling, detailed low-degree consequences, and
   the spectral--lattice one-rectangle criterion.
8. `docs/PRIORITY_AND_PROTOCOL_AUDIT.md` for the targeted novelty comparison
   and the end-to-end communication-wrapper audit.

## Headline evidence map

| Claim | Paper evidence | Lean core | Computational audit |
|---|---|---|---|
| Global sharp interior-layer `2/5` escape and unique equality | Six-coordinate fibre counts and `ζ` derivation | Cleared polynomial and unique zero in `SharpSixCoordinateGap`; not the fibre count or `ζ` derivation | Six-coordinate certificate is the sharp machine evidence (123,750 parameters); 2,047,045 adjacent intervals are an independent exhaustive audit |
| Interior Johnson-product logarithmic protocol and selector boundary | Row classification, rank-sensitive protocol, and `k_i=1` embedding | Equal-block middle-layer arithmetic and the block-dependent affine kernel; no protocol, `D(M)`, or `rect(M)` theorem | 2,533,728 row-column checks and 5,400 general-product protocol cases |
| Sparse Johnson-column logarithmic bounds | Explicit cross, unisolvent transfer, robust sampling, covariance gap, and Hadamard construction | Relation lifting, `f(f-1)` certificate, local affine pairing, covariance contradiction, and threshold arithmetic; no communication theorem | 3,060 quadratic-cross actual-rank protocol row families, 9,241,290 affine evaluations, and six Hadamard designs |

## Auxiliary evidence

- `SharpThreeMarkedGap` and `SharpLowDensityGap` certify the short-side and
  low-density cleared-polynomial subproofs.
- `JuntaRankPooling`, `RankBound`, and binary `CoordinateDecisionTree`
  cover ingredients of rank-pooled query transfer; the paper's `Q`-ary tree
  and complete protocols are not formalized.
- The low-degree degree-to-query bounds are literature inputs, not new
  formalized results.

## What is deliberately omitted

The original research workspace contains historical Fourier, affine-section,
rectangle-extraction, and exploratory Lean modules. They are not dependencies
of the headline claims above and are intentionally excluded. The curated core
contains no generated `.olean` files, caches, screenshots, temporary output,
or abandoned proof routes.

Also outside the Lean boundary are Chernoff/VC/DPP arguments, the Filmus,
Dafni--Filmus--Lifshitz--Lindzey--Vinyals, and Midrijānis literature inputs,
the explicit cross `Y_×`, complete protocol wrappers, and claims about
`D(M)` or `rect(M)`.

## Reviewer commands

```bash
make verify-python
make verify-lean
make paper
```

All programs fail by assertion or nonzero exit status if a certified identity
or count changes.
