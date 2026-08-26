import Mathlib

namespace AffineSectionLogRank

/-- The elementary half-box inequality used to lower-bound the variance of a
hypergeometric law after complementing both parameters into `[0, 1/2]`. -/
theorem half_box_complement_product
    (p q : ℝ) (hp : p ≤ 1 / 2) (hq : q ≤ 1 / 2) :
    1 / 2 - p * q ≤ (1 - p) * (1 - q) := by
  have hprod : 0 ≤ (1 - 2 * p) * (1 - 2 * q) := by
    exact mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Arithmetic core of the `Var ≥ 1/3` step: if `1 ≤ μ ≤ N/4` and
`N ≥ 4`, then the normalized quadratic variance lower envelope is at least
`1/3`. -/
theorem hypergeometric_variance_quadratic_core
    (N μ : ℝ) (hN : 4 ≤ N) (hμ1 : 1 ≤ μ) (hμN : 4 * μ ≤ N) :
    1 / 3 ≤ μ * (N - 2 * μ) / (2 * (N - 1)) := by
  have hfactor₁ : 0 ≤ μ - 1 := by linarith
  have hfactor₂ : 0 ≤ N - 2 * μ - 2 := by linarith
  have hproduct : 0 ≤ (μ - 1) * (N - 2 * μ - 2) :=
    mul_nonneg hfactor₁ hfactor₂
  have hden : 0 < 2 * (N - 1) := by linarith
  have hnumerator : 2 * (N - 1) / 3 ≤ μ * (N - 2 * μ) := by
    nlinarith
  apply (le_div_iff₀ hden).2
  calc
    (1 / 3) * (2 * (N - 1)) = 2 * (N - 1) / 3 := by ring
    _ ≤ μ * (N - 2 * μ) := hnumerator

/-- Exact rational checks in the log-concave tail calculation. -/
theorem log_concave_escape_constant_chain :
    (2 / 63 : ℝ) < 1 / 25 ∧
      (135 / 32 : ℝ) < 17 / 4 ∧
      (81 / 256 : ℝ) < 1 / 3 := by
  norm_num

/-- A lower bound on the short-side density immediately squares to the
quadratic detector parameter. -/
theorem quadratic_balance_parameter
    (β p : ℝ) (hβ : 0 ≤ β) (hβp : β ≤ p) :
    β ^ 2 / 16 ≤ p ^ 2 / 16 := by
  nlinarith

end AffineSectionLogRank
