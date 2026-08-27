import Mathlib

namespace AffineSectionLogRank

/-- Cleared-denominator polynomial for the central two-tail mass when the
marked short side has size three and n = 2k + t. -/
def threeMarkedCentralPolynomial (k t : ℝ) : ℝ :=
  12 * k ^ 2 * (k - 1) * (k - 3) +
  (32 * k ^ 3 - 84 * k ^ 2 + 40 * k) * t +
  (43 * k ^ 2 - 60 * k + 10) * t ^ 2 +
  (25 * k - 15) * t ^ 3 + 5 * t ^ 4

/-- After shifting k = q + 3, every coefficient of the central-tail
polynomial is nonnegative. -/
theorem threeMarkedCentralPolynomial_shift (q t : ℝ) :
    threeMarkedCentralPolynomial (q + 3) t =
      12 * q ^ 4 + 96 * q ^ 3 + 252 * q ^ 2 + 216 * q +
      (32 * q ^ 3 + 204 * q ^ 2 + 400 * q + 228) * t +
      (43 * q ^ 2 + 198 * q + 217) * t ^ 2 +
      (25 * q + 60) * t ^ 3 + 5 * t ^ 4 := by
  simp [threeMarkedCentralPolynomial]
  ring

/-- The central-tail polynomial is nonnegative for k ≥ 3, with its unique
zero at k = 3, t = 0. -/
theorem threeMarkedCentralPolynomial_eq_zero_iff
    (k t : ℝ) (hk : 3 ≤ k) (ht : 0 ≤ t) :
    threeMarkedCentralPolynomial k t = 0 ↔ k = 3 ∧ t = 0 := by
  let q := k - 3
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hkq : k = q + 3 := by dsimp [q]; ring
  rw [hkq, threeMarkedCentralPolynomial_shift]
  constructor
  · intro hzero
    have hrest :
        0 ≤
          12 * q ^ 4 + 96 * q ^ 3 + 252 * q ^ 2 +
          (32 * q ^ 3 + 204 * q ^ 2 + 400 * q) * t +
          (43 * q ^ 2 + 198 * q) * t ^ 2 +
          217 * t ^ 2 + (25 * q + 60) * t ^ 3 + 5 * t ^ 4 := by
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

/-- At the exceptional short-side boundary `k = 2`, the polynomial agrees
term-by-term with the manuscript formula
`F(2,t) = -48 + 62 t^2 + 35 t^3 + 5 t^4`. -/
theorem threeMarkedCentralPolynomial_two_formula (t : ℝ) :
    threeMarkedCentralPolynomial 2 t =
      -48 + 62 * t ^ 2 + 35 * t ^ 3 + 5 * t ^ 4 := by
  simp [threeMarkedCentralPolynomial]
  ring

/-- The manuscript's `k = 2` short-edge branch: `t ≥ 2` makes the central
polynomial strictly positive. -/
theorem threeMarkedCentralPolynomial_two_pos
    (t : ℝ) (ht : 2 ≤ t) :
    0 < threeMarkedCentralPolynomial 2 t := by
  rw [threeMarkedCentralPolynomial_two_formula]
  have hshift :
      -48 + 62 * t ^ 2 + 35 * t ^ 3 + 5 * t ^ 4 =
        5 * (t - 2) ^ 4 + 75 * (t - 2) ^ 3 +
        392 * (t - 2) ^ 2 + 828 * (t - 2) + 560 := by
    ring
  rw [hshift]
  have hnonneg : 0 ≤ t - 2 := by linarith
  positivity

/-- Cleared-denominator polynomial for the other potentially minimal tail. -/
def threeMarkedOtherPolynomial (k t : ℝ) : ℝ :=
  16 * k * (k - 1) * (2 * k - 1) +
  (42 * k ^ 2 - 54 * k + 10) * t +
  (13 * k - 15) * t ^ 2

/-- The other tail is always strictly above the proposed sharp bound. -/
theorem threeMarkedOtherPolynomial_pos
    (k t : ℝ) (hk : 2 ≤ k) (ht : 0 ≤ t) :
    0 < threeMarkedOtherPolynomial k t := by
  let q := k - 2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hkq : k = q + 2 := by dsimp [q]; ring
  rw [hkq]
  have hfirst : 0 < 16 * (q + 2) * (q + 1) * (2 * q + 3) := by
    positivity
  have hsecond : 0 ≤ (42 * q ^ 2 + 114 * q + 70) * t := by
    positivity
  have hthird : 0 ≤ (13 * q + 11) * t ^ 2 := by
    positivity
  simp [threeMarkedOtherPolynomial]
  nlinarith

end AffineSectionLogRank
