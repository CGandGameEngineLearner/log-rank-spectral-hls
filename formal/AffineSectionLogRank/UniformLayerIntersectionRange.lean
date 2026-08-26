import Mathlib

namespace AffineSectionLogRank

/-- Width of the integer interval of possible intersections between a fixed
`s`-subset and all `k`-subsets of an `n`-set. -/
def uniformIntersectionRangeWidth (n k s : ℕ) : ℕ :=
  min k s - (k - (n - s))

/-- In the interior of both the row-size and layer-size ranges, the possible
intersection interval contains at least three integers. -/
theorem two_le_uniformIntersectionRangeWidth
    (n k s : ℕ)
    (hklo : 2 ≤ k) (hkhi : k ≤ n - 2)
    (hslo : 2 ≤ s) (hshi : s ≤ n - 2) :
    2 ≤ uniformIntersectionRangeWidth n k s := by
  unfold uniformIntersectionRangeWidth
  by_cases hkns : k ≤ n - s
  · have hlower : k - (n - s) = 0 := Nat.sub_eq_zero_of_le hkns
    rw [hlower]
    exact le_min hklo hslo
  · have hnsk : n - s < k := by omega
    by_cases hks : k ≤ s
    · rw [Nat.min_eq_left hks]
      omega
    · have hsk : s ≤ k := by omega
      rw [Nat.min_eq_right hsk]
      omega

/-- If the intersection range has width at most one on a nontrivial layer,
then the fixed set is empty/singleton or co-singleton/full. -/
theorem small_or_cosmall_of_uniformIntersectionRangeWidth_le_one
    (n k s : ℕ)
    (hklo : 2 ≤ k) (hkhi : k ≤ n - 2)
    (hwidth : uniformIntersectionRangeWidth n k s ≤ 1) :
    s ≤ 1 ∨ n - s ≤ 1 := by
  by_contra h
  push_neg at h
  have hslo : 2 ≤ s := by omega
  have hshi : s ≤ n - 2 := by omega
  have := two_le_uniformIntersectionRangeWidth n k s hklo hkhi hslo hshi
  omega

end AffineSectionLogRank
