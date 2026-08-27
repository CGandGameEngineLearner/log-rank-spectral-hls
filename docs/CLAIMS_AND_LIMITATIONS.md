# Claims and limitations

## Proved

- A globally sharp interior-hypergeometric adjacent-pair escape bound with constant
  `2/5` and unique equality `(6,3,3,1)`.
- An interior product-Johnson classification and logarithmic protocol, with
  `D(M) <= ceil(log2(rank(M)+1))+4`, rectangle density at least
  `1/(4(d+1))`, and a `k_i=1` selector embedding of arbitrary Boolean
  matrices.
- Sparse Johnson-column logarithmic bounds: the explicit quadratic
  unisolvent cross, anchor-free β²/10 deletion robustness, the deterministic
  covariance threshold `n/(8(n-2))`, and explicit minimal
  Sylvester--Hadamard columns.

## Not proved

- The general Log-Rank Conjecture for arbitrary Boolean matrices.
- A universal improvement over the general `O(sqrt(rank))` communication
  bound.
- An explicit `O_beta(n)` no-anchor construction for every balanced pair
  `(n,k)`; the explicit Hadamard construction covers an infinite central
  sequence.
- Full Lean formalization of every analytic/probabilistic theorem in the
  manuscript.

## Lean coverage boundary

The curated Lean development proves algebraic and finite-combinatorial cores,
not the paper's communication theorems. In particular:

- `SharpSixCoordinateGap` proves nonnegativity of the cleared polynomial and
  its unique zero; the six-coordinate fibre count and `ζ` derivation remain
  paper arguments.
- `UnisolventRestriction` contains the trivial-kernel definition, finite
  relation lifting, and the `f(f-1)` Booleanity certificate.
- `AffineSupportPairing` is a local exchange-pair lemma, while
  `CoordinateDecisionTree` treats binary rather than `Q`-ary trees.
- `ProductJohnsonArithmetic` covers equal-block middle layers `k=n/2`, not
  the general weighted variance `V(s)`.
- Chernoff/VC/DPP, the Filmus, Dafni--Filmus--Lifshitz--Lindzey--Vinyals, and
  Midrijānis inputs, the explicit cross `Y_×`, complete protocol wrappers,
  and conclusions about `D(M)` or `rect(M)` are not formalized.

## Review status

The results have internal proof audits, exhaustive computations, and a
curated Lean core. They have not yet received independent peer review or a
complete external priority search.
