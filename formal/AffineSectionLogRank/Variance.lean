import Mathlib

namespace AffineSectionLogRank

theorem bernoulli_variance_le_quarter (p : ℝ) :
    p * (1 - p) ≤ (1 : ℝ) / 4 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

theorem two_consecutive_variance_le_quarter (u p : ℝ) :
    p * (u + 1 - (u + p)) ^ 2
      + (1 - p) * (u - (u + p)) ^ 2 ≤ (1 : ℝ) / 4 := by
  ring_nf
  nlinarith [sq_nonneg (p - 1 / 2)]

theorem uniformSliceVariance_algebra
    (d k s : ℝ) (hd : d ≠ 0) (hd1 : d ≠ 1) :
    s * (k / d) * (1 - k / d)
        + s * (s - 1) *
          (k * (k - 1) / (d * (d - 1)) - (k / d) ^ 2)
      =
    s * (d - s) * k * (d - k) / (d ^ 2 * (d - 1)) := by
  have hdm1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd1
  field_simp [hd, hdm1]
  ring

end AffineSectionLogRank
