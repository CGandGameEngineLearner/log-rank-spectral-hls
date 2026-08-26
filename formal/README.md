# Curated Lean core

This directory contains the reviewer-facing Lean 4.22 core for the headline
claims. It intentionally omits the older Fourier, affine-section, extraction,
and exploratory modules from the research workspace.

Build from this directory with:

```bash
lake update
lake build
```

The 18 retained modules cover:

- two-point variance and the real-rank factorization;
- unisolvent restriction and affine support pairing;
- rank pooling and coordinate decision trees;
- product-Johnson range and kernel lemmas;
- the global sharp hypergeometric `2/5` polynomial certificates;
- deterministic covariance-gap arithmetic and the Hadamard threshold.

The Lean development certifies the finite algebraic/combinatorial core. The
probabilistic sampling theorems, VC theorem invocation, and the full paper
assembly remain conventional paper proofs and are identified as such in
`FORMALIZATION_MANIFEST.md`.
