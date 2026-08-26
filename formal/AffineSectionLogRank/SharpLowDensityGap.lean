import Mathlib

namespace AffineSectionLogRank

/-- Cleared-denominator difference between the four-coordinate fiber bound
and the proposed sharp two-fifths bound after writing n = 3k + t. -/
def lowDensityFiberPolynomial (k t : ℝ) : ℝ :=
  6 * k ^ 4 + 18 * k ^ 3 - 36 * k ^ 2 + 12 * k +
  (26 * k ^ 3 - 33 * k ^ 2 + 3 * k) * t +
  (17 * k ^ 2 - 28 * k + 5) * t ^ 2 +
  (3 * k - 5) * t ^ 3

/-- Shifting k = q + 2 exposes strictly positive coefficients. -/
theorem lowDensityFiberPolynomial_shift (q t : ℝ) :
    lowDensityFiberPolynomial (q + 2) t =
      6 * q ^ 4 + 66 * q ^ 3 + 216 * q ^ 2 + 276 * q + 120 +
      (26 * q ^ 3 + 123 * q ^ 2 + 183 * q + 82) * t +
      (17 * q ^ 2 + 40 * q + 17) * t ^ 2 +
      (3 * q + 1) * t ^ 3 := by
  simp [lowDensityFiberPolynomial]
  ring

/-- The low-density four-coordinate certificate is strictly stronger than
the two-fifths quadratic target. -/
theorem lowDensityFiberPolynomial_pos
    (k t : ℝ) (hk : 2 ≤ k) (ht : 0 ≤ t) :
    0 < lowDensityFiberPolynomial k t := by
  let q := k - 2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hkq : k = q + 2 := by dsimp [q]; ring
  rw [hkq, lowDensityFiberPolynomial_shift]
  positivity

end AffineSectionLogRank
