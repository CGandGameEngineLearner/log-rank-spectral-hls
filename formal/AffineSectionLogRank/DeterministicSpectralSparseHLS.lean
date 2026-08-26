import Mathlib

namespace AffineSectionLogRank

/-- Arithmetic core of the deterministic covariance-gap theorem.  A medium
row size, the spectral lower bound, and two-point variance at most one quarter
cannot coexist. -/
theorem spectral_medium_variance_contradiction
    (n m lambda variance : ℝ)
    (hn : 4 ≤ n) (hmlo : 2 ≤ m) (hmhi : m ≤ n - 2)
    (hlambda : n / (8 * (n - 2)) < lambda)
    (hvarianceLower : lambda * (m * (n - m) / n) ≤ variance)
    (hvarianceUpper : variance ≤ 1 / 4) : False := by
  have hnpos : 0 < n := by linarith
  have hnm2 : 0 < n - 2 := by linarith
  have hden : 0 < 8 * (n - 2) := mul_pos (by norm_num) hnm2
  have hlambdaPos : 0 < lambda := by
    have hratioPos : 0 < n / (8 * (n - 2)) := div_pos hnpos hden
    linarith
  have hleft : 0 ≤ m - 2 := by linarith
  have hright : 0 ≤ n - m - 2 := by linarith
  have hproduct : 0 ≤ (m - 2) * (n - m - 2) :=
    mul_nonneg hleft hright
  have hshape : 2 * (n - 2) ≤ m * (n - m) := by
    nlinarith
  have hlambdaMul : n < lambda * (8 * (n - 2)) :=
    (div_lt_iff₀ hden).mp hlambda
  have hscaled :
      lambda * (2 * (n - 2)) ≤ lambda * (m * (n - m)) := by
    exact mul_le_mul_of_nonneg_left hshape hlambdaPos.le
  have hquarter : 1 / 4 < lambda * (m * (n - m) / n) := by
    rw [show lambda * (m * (n - m) / n) =
      (lambda * (m * (n - m))) / n by ring]
    apply (lt_div_iff₀ hnpos).2
    nlinarith
  linarith

/-- The covariance eigenvalue of every nontrivial Sylvester--Hadamard design
lies strictly above the deterministic spectral HLS threshold. -/
theorem sylvester_hadamard_covariance_above_threshold
    (u : ℝ) (hu : 2 ≤ u) :
    (4 * u - 1) / (8 * (4 * u - 3)) < u / (4 * u - 1) := by
  have hleft : 0 < 4 * u - 1 := by linarith
  have hright : 0 < 8 * (4 * u - 3) := by nlinarith
  apply (div_lt_div_iff₀ hright hleft).2
  nlinarith

end AffineSectionLogRank
