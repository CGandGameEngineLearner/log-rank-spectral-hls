import AffineSectionLogRank.ProductJohnsonArithmetic
import AffineSectionLogRank.UniformLayerIntersectionRange

open scoped BigOperators

namespace AffineSectionLogRank

def productIntersectionRangeWidth {ι : Type*} [Fintype ι]
    (blockSize layerSize rowSize : ι → ℕ) : ℕ :=
  ∑ i, uniformIntersectionRangeWidth (blockSize i) (layerSize i) (rowSize i)

theorem minority_le_rangeWidth_of_minority_le_one
    (n k s : ℕ)
    (hklo : 2 ≤ k) (hkhi : k ≤ n - 2)
    (hs : s ≤ n)
    (hminor : localMinority n s ≤ 1) :
    localMinority n s ≤ uniformIntersectionRangeWidth n k s := by
  unfold localMinority uniformIntersectionRangeWidth at *
  by_cases hsn : s ≤ n - s
  · rw [Nat.min_eq_left hsn] at hminor ⊢
    have hcases : s = 0 ∨ s = 1 := by omega
    rcases hcases with rfl | rfl
    · simp
    · simp
      omega
  · have hns : n - s ≤ s := by omega
    rw [Nat.min_eq_right hns] at hminor ⊢
    have hcases : n - s = 0 ∨ n - s = 1 := by omega
    rcases hcases with hzero | hone
    · have hseq : s = n := by omega
      subst s
      simp
    · have hseq : s = n - 1 := by omega
      have hkn : k ≤ n - 1 := by omega
      rw [hseq]
      simp [Nat.min_eq_left hkn]
      omega

/-- For interior product layers, total intersection-range width at most one
forces total Hamming distance from a block union at most one. -/
theorem product_minority_le_one_of_rangeWidth_le_one
    {ι : Type*} [Fintype ι]
    (blockSize layerSize rowSize : ι → ℕ)
    (hinterior : ∀ i, 2 ≤ layerSize i ∧ layerSize i ≤ blockSize i - 2)
    (hrow : ∀ i, rowSize i ≤ blockSize i)
    (hwidth : productIntersectionRangeWidth blockSize layerSize rowSize ≤ 1) :
    (∑ i, localMinority (blockSize i) (rowSize i)) ≤ 1 := by
  classical
  have hlocal : ∀ i, localMinority (blockSize i) (rowSize i) ≤ 1 := by
    intro i
    by_contra hbad
    have htwo : 2 ≤ localMinority (blockSize i) (rowSize i) := by omega
    have hwidthTwo := two_le_uniformIntersectionRangeWidth
      (blockSize i) (layerSize i) (rowSize i)
      (hinterior i).1 (hinterior i).2
      (by
        by_contra hsbad
        have : rowSize i ≤ 1 := by omega
        unfold localMinority at htwo
        omega)
      (by
        by_contra hsbad
        have : blockSize i - rowSize i ≤ 1 := by omega
        unfold localMinority at htwo
        omega)
    have hsingle :
        uniformIntersectionRangeWidth (blockSize i) (layerSize i) (rowSize i) ≤
          productIntersectionRangeWidth blockSize layerSize rowSize := by
      unfold productIntersectionRangeWidth
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun j => uniformIntersectionRangeWidth
          (blockSize j) (layerSize j) (rowSize j))
        (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      simpa using hs
    omega
  calc
    (∑ i, localMinority (blockSize i) (rowSize i)) ≤
        ∑ i, uniformIntersectionRangeWidth
          (blockSize i) (layerSize i) (rowSize i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact minority_le_rangeWidth_of_minority_le_one
        (blockSize i) (layerSize i) (rowSize i)
        (hinterior i).1 (hinterior i).2 (hrow i) (hlocal i)
    _ = productIntersectionRangeWidth blockSize layerSize rowSize := rfl
    _ ≤ 1 := hwidth

end AffineSectionLogRank
