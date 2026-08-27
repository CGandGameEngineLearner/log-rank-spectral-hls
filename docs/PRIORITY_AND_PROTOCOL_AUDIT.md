# Priority and protocol audit

Audit date: August 26, 2026.

This document records the targeted prior-art comparison and the end-to-end
paper proof audit for the three reviewer-facing risks. It is evidence of a
focused search, not a substitute for an independent MathSciNet review or
expert priority opinion.

## 1. Sharp hypergeometric 2/5 escape

The audited statement is restricted to 2 <= k <= n-2 and
2 <= |A| <= n-2:

    Pr[|A intersect B| not in {a,a+1}]
      >= (2/5) (min(k,n-k)/n)^2,

with unique equality (n,k,|A|,a)=(6,3,3,1).

The search covered the following neighboring lines.

- Hush--Scovel, Concentration of the Hypergeometric Distribution, gives
  deviation-from-the-mean tail estimates, not the maximum mass of an
  arbitrary adjacent pair and not the 2/5 equality classification:
  https://doi.org/10.1016/j.spl.2005.05.019
- Sgall, Bounds on Pairs of Families with Restricted Intersections, and
  Keevash--Sudakov, On a Restricted Cross-Intersection Problem, optimize
  absolute products of two set families rather than normalized escape
  inside one prescribed complete Johnson layer:
  https://doi.org/10.1007/s004939970007 and
  https://doi.org/10.1016/j.jcta.2005.11.006
- Hambardzumyan--Lovett--Shirley formulate the cross-intersection
  equivalence, including the adjacent-value special case, but do not prove
  this local hypergeometric constant:
  https://doi.org/10.4230/LIPIcs.CCC.2026.7
  (preprint: https://arxiv.org/abs/2510.02583)

No exact predecessor for the normalized 2/5 inequality or its unique
equality case was found in these searches. The manuscript now calls it a
candidate new sharp inequality and explicitly requests independent priority
confirmation.

## 2. Johnson-product novelty boundary

The local classification is not claimed as new.

- Filmus--Ihringer call the Johnson degree-one classification folklore and
  note several earlier appearances; their Theorem 1.2 classifies constants,
  coordinates, and complements:
  https://arxiv.org/abs/1801.06034
- Their Lemma 8.1 is the local multislice input.
- The observation that a Boolean additive degree-one function on a Cartesian
  product has at most one nonconstant factor is elementary.

The candidate additions are limited to the prescribed Johnson-product right
family, the bound on the used coordinate set in terms of the actual
restricted real rank, the resulting logarithmic protocol and relative
rectangle, and their unequal-block assembly. The k_i=1 selector is presented
as a boundary witness, not as a new classification theorem.

Kupavskii--Weltge prove the absolute bound |A||B| <= (d+1)2^d for full-span
binary scalar products; this does not produce a relative rectangle inside a
specified sparse Johnson product:
https://arxiv.org/abs/2008.07153

Sudakov--Tomon apply to arbitrary rank-r Boolean matrices and give the
general 2^{-O(sqrt(r))} rectangle. The logarithmic result here is stronger
only on the restricted product/sparse-column classes:
https://doi.org/10.1007/s10107-024-02117-9

## 3. End-to-end protocol audit

### Quadratic unisolvent columns

1. Degree-two unisolvence makes f(f-1)=0 on the full slice, so every affine
   row that is Boolean on the sparse columns is Boolean ambiently.
2. The same unisolvence lifts every linear row relation; therefore the
   ambient and restricted matrices have the same real rank r.
3. The interior Johnson classification leaves only constants, coordinates,
   and coordinate complements.
4. Choose r basis rows. Their coordinates form a pool of size at most r;
   depth-one symmetry needs at most one additional representative, so all
   nonconstant rows query a common universe of size at most r+1.
5. If the common universe is nonempty, constant rows can query an arbitrary
   coordinate and ignore the reply. Nonconstant rows send the coordinate
   index, receive one membership bit, and apply the locally known
   complement. This costs ceil(log2(r+1))+1 bits.
6. Because the convention requires only Alice to output, transcripts are
   not used to infer a rectangle. Rows are instead pigeonholed by coordinate
   (or the constant group), then by orientation/value, and columns by the
   queried bit. The total loss is at most 4(r+1).

### Random and deletion-robust columns

- The sharp escape event is required only for medium rows
  2 <= |A| <= n-2; singleton and co-singleton rows are the permitted
  coordinate cases.
- VC uniform convergence preserves every nonzero affine support, hence
  degree-one unisolvence and actual rank after deletion.
- The detector event removes every medium row, leaving exactly
  empty/full/singleton/co-singleton rows.
- The allowed deletion is one quarter of the smaller detector/unisolvence
  margin. On a beta-balanced layer both margins are at least 2 beta^2/5,
  yielding the stated beta^2/10 fraction.
- In the protected-anchor variant the retained family is explicitly
  Y_0 union (Y_1 minus D), so overlap between anchor and sample cannot
  accidentally delete an anchor column.

### Deterministic covariance columns

- The threshold lambda > n/(8(n-2)) forces every medium row to have
  variance greater than 1/4, contradicting two-point support.
- The same positive covariance gap proves degree-one unisolvence and actual
  rank preservation.
- The remaining rows use the same depth-one wrapper above.

### Product Johnson columns

- The variance/range argument classifies rows as constants, coordinates, or
  complements.
- For a used coordinate set S, full blocks give exactly the fixed-sum
  relations; hence rank(X_S)=|S|-f+1 when f>0.
- Interior blocks have size at least four, so f <= |S|/4 and
  |S| <= 4(r+1)/3 after the rank-one constant perturbation.
- The resulting message count satisfies the stated ceil(log2(r+1))+4 bound.

## Issues found and corrected

- Added the missing hypothesis 2 <= k <= n-2 to the sharp theorem and
  headline statements; the literal boundary statement was false for k=1.
- Replaced the false phrase "every nontrivial A" by the correct medium-row
  range 2 <= |A| <= n-2 in the low-density and detector statements.
- Made the actual-rank lifting and complete depth-one protocol explicit.
- Replaced the invalid one-party-transcript shortcut by a direct
  row-type/column-fibre proof of the rectangle bound.
- Made the protected-anchor deletion semantics explicit when the random
  sample overlaps the anchor.

Lean continues to certify only the algebraic cores listed in
formal/FORMALIZATION_MANIFEST.md; this audit does not recast the protocol as
machine-formalized.
