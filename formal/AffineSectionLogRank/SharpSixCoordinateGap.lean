import Mathlib

namespace AffineSectionLogRank

/-- Cleared-denominator difference between the six-coordinate all-trace
certificate and the sharp two-fifths quadratic target, with n = 2k + t. -/
def sixCoordinateSharpPolynomial (k t : ℝ) : ℝ :=
  16 * k ^ 6 - 60 * k ^ 5 - 80 * k ^ 4 +
  540 * k ^ 3 - 656 * k ^ 2 + 240 * k +
  (120 * k ^ 5 - 660 * k ^ 4 + 1160 * k ^ 3 -
    720 * k ^ 2 + 112 * k) * t +
  (230 * k ^ 4 - 1095 * k ^ 3 + 1760 * k ^ 2 -
    1125 * k + 220) * t ^ 2 +
  (195 * k ^ 3 - 690 * k ^ 2 + 800 * k - 315) * t ^ 3 +
  (80 * k ^ 2 - 180 * k + 110) * t ^ 4 +
  (13 * k - 15) * t ^ 5

/-- Shifting k = q + 3 exposes nonnegative coefficients and the unique
possible zero. -/
theorem sixCoordinateSharpPolynomial_shift (q t : ℝ) :
    sixCoordinateSharpPolynomial (q + 3) t =
      16 * q ^ 6 + 228 * q ^ 5 + 1180 * q ^ 4 + 2820 * q ^ 3 +
      3124 * q ^ 2 + 1272 * q +
      (120 * q ^ 5 + 1140 * q ^ 4 + 4040 * q ^ 3 +
        6480 * q ^ 2 + 4432 * q + 876) * t +
      (230 * q ^ 4 + 1665 * q ^ 3 + 4325 * q ^ 2 +
        4710 * q + 1750) * t ^ 2 +
      (195 * q ^ 3 + 1065 * q ^ 2 + 1925 * q + 1140) * t ^ 3 +
      (80 * q ^ 2 + 300 * q + 290) * t ^ 4 +
      (13 * q + 24) * t ^ 5 := by
  simp [sixCoordinateSharpPolynomial]
  ring

/-- For k at least three, the six-coordinate sharp polynomial has the unique
zero k = 3, t = 0. -/
theorem sixCoordinateSharpPolynomial_eq_zero_iff
    (k t : ℝ) (hk : 3 ≤ k) (ht : 0 ≤ t) :
    sixCoordinateSharpPolynomial k t = 0 ↔ k = 3 ∧ t = 0 := by
  let q := k - 3
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hkq : k = q + 3 := by dsimp [q]; ring
  rw [hkq, sixCoordinateSharpPolynomial_shift]
  constructor
  · intro hzero
    have hrest :
        0 ≤
          16 * q ^ 6 + 228 * q ^ 5 + 1180 * q ^ 4 + 2820 * q ^ 3 +
          3124 * q ^ 2 +
          (120 * q ^ 5 + 1140 * q ^ 4 + 4040 * q ^ 3 +
            6480 * q ^ 2 + 4432 * q) * t +
          (230 * q ^ 4 + 1665 * q ^ 3 + 4325 * q ^ 2 +
            4710 * q) * t ^ 2 +
          (195 * q ^ 3 + 1065 * q ^ 2 + 1925 * q) * t ^ 3 +
          (80 * q ^ 2 + 300 * q) * t ^ 4 +
          290 * t ^ 4 + (13 * q + 24) * t ^ 5 := by
      positivity
    have hqzero : q = 0 := by nlinarith
    have htzero : t = 0 := by nlinarith
    constructor
    · dsimp [q] at hqzero
      linarith
    · exact htzero
  · rintro ⟨hk3, ht0⟩
    have hq0 : q = 0 := by linarith
    rw [hq0, ht0]
    norm_num

/-- The exceptional k = 2 boundary becomes strictly positive after t = s+2. -/
theorem sixCoordinateSharpPolynomial_two_shift (s : ℝ) :
    sixCoordinateSharpPolynomial 2 (s + 2) =
      11 * s ^ 5 + 180 * s ^ 4 + 1085 * s ^ 3 +
      3000 * s ^ 2 + 3764 * s + 1680 := by
  simp [sixCoordinateSharpPolynomial]
  ring

theorem sixCoordinateSharpPolynomial_two_pos
    (t : ℝ) (ht : 2 ≤ t) :
    0 < sixCoordinateSharpPolynomial 2 t := by
  let s := t - 2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hts : t = s + 2 := by dsimp [s]; ring
  rw [hts, sixCoordinateSharpPolynomial_two_shift]
  positivity

end AffineSectionLogRank
