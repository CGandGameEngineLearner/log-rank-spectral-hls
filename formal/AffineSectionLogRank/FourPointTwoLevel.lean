import Mathlib

namespace AffineSectionLogRank

def realTwoLevel (x : ℝ) : Prop := x = 0 ∨ x = 1

/-- A nondegenerate affine image of a Boolean square cannot have all four
corners in the two-point set `{0,1}`.  Conditioning on all other variables
therefore gives the sharp elementary probability bound `3/4`. -/
theorem not_all_four_affine_corners_twoLevel
    (c a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬(realTwoLevel c ∧
      realTwoLevel (c + a) ∧
      realTwoLevel (c + b) ∧
      realTwoLevel (c + a + b)) := by
  rintro ⟨hc, hca, hcb, hcab⟩
  rcases hc with hc | hc <;>
    rcases hca with hca | hca <;>
    rcases hcb with hcb | hcb <;>
    rcases hcab with hcab | hcab <;>
    simp_all

end AffineSectionLogRank
