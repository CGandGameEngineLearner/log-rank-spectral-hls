# Formalization manifest

Lean version: 4.22.0. Mathlib revision: `v4.22.0`.

| Paper component | Module | Coverage |
|---|---|---|
| Two-consecutive-value variance algebra | `Variance` | Complete algebraic core |
| Unisolvent restriction core | `UnisolventRestriction` | Trivial-kernel definition, finite-relation lifting, and the `f(f-1)` Booleanity certificate; no communication theorem |
| Affine support swap pair | `AffineSupportPairing` | Local exchange-pair lemma only; not the global support-cardinality bound |
| Rank-basis support pooling | `JuntaRankPooling` | Complete abstract core |
| Decision-tree support bounds | `CoordinateDecisionTree` | Binary trees only; the paper's `Q`-ary trees are not formalized |
| Uniform-layer affine kernel | `UniformLayerConstantSum` | Complete |
| Interior intersection range | `UniformLayerIntersectionRange` | Complete |
| Product variance/range arithmetic | `ProductJohnsonArithmetic`, `ProductInteriorRange` | `ProductJohnsonArithmetic` covers equal-block middle layers `k=n/2`, not the general weighted `V(s)`; the local interior-range arithmetic is formalized separately |
| Product affine kernel | `ProductLayerKernel` | Block-dependent ground types and layer sizes `k_i`; no protocol wrapper |
| Boolean additive one-factor obstruction | `FourPointTwoLevel`, `BooleanProductOneFactor` | Complete |
| Preliminary quadratic constants | `QuadraticGapArithmetic` | Complete arithmetic core |
| Deterministic spectral threshold | `DeterministicSpectralSparseHLS` | Complete arithmetic core |
| Sharp short-side `2/5` polynomials | `SharpThreeMarkedGap` | Complete |
| Sharp low-density polynomial | `SharpLowDensityGap` | Complete |
| Global six-coordinate sharp polynomial | `SharpSixCoordinateGap` | Cleared-polynomial nonnegativity and unique zero only; the six-coordinate fibre count and `ζ` derivation remain in the paper |
| Rank at most `d+1` factorization | `RankBound` | Complete |

Not formalized here: matrix Chernoff/VC sampling, the projection-DPP
construction, the Filmus, Dafni--Filmus--Lifshitz--Lindzey--Vinyals, and
Midrijānis literature inputs, the explicit cross `Y_×`, the complete
communication-protocol wrappers, and conclusions about `D(M)` or `rect(M)`.
