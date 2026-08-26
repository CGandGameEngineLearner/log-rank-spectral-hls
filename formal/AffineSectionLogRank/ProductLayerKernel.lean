import AffineSectionLogRank.UniformLayerConstantSum

open scoped BigOperators

namespace AffineSectionLogRank

/-- The kernel of evaluation on a complete product of nontrivial uniform
layers has block-constant coordinate coefficients. -/
theorem productLayerKernel_block_constant
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (k : ℕ) (weight : ι → α → ℝ) (constant : ℝ)
    (hkpos : 1 ≤ k) (hklt : k < Fintype.card α)
    (hzero : ∀ column : ι → Finset α,
      (∀ i, (column i).card = k) →
      constant + ∑ i, ∑ x ∈ column i, weight i x = 0) :
    ∀ i x y, weight i x = weight i y := by
  classical
  have hkcard : k ≤ (Finset.univ : Finset α).card := by
    simpa using hklt.le
  obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hkcard
  intro i
  apply constant_of_sum_eq_on_powersetCard k (weight i)
    (∑ x ∈ U, weight i x) hkpos hklt
  intro S hScard
  let columnS : ι → Finset α := fun j => if j = i then S else U
  let columnU : ι → Finset α := fun _ => U
  have hcardS : ∀ j, (columnS j).card = k := by
    intro j
    by_cases hji : j = i
    · simp [columnS, hji, hScard]
    · simp [columnS, hji, hUcard]
  have hcardU : ∀ j, (columnU j).card = k := by
    intro j
    simp [columnU, hUcard]
  have hzS := hzero columnS hcardS
  have hzU := hzero columnU hcardU
  have heraseS :
      (∑ j ∈ (Finset.univ : Finset ι).erase i,
        ∑ x ∈ columnS j, weight j x) =
      ∑ j ∈ (Finset.univ : Finset ι).erase i,
        ∑ x ∈ U, weight j x := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [columnS, hji]
  have hsumS :
      (∑ j, ∑ x ∈ columnS j, weight j x) =
        (∑ x ∈ S, weight i x) +
          ∑ j ∈ (Finset.univ : Finset ι).erase i,
            ∑ x ∈ U, weight j x := by
    calc
      (∑ j, ∑ x ∈ columnS j, weight j x) =
          (∑ x ∈ columnS i, weight i x) +
            ∑ j ∈ (Finset.univ : Finset ι).erase i,
              ∑ x ∈ columnS j, weight j x :=
        (Finset.add_sum_erase (Finset.univ : Finset ι)
          (fun j => ∑ x ∈ columnS j, weight j x)
          (Finset.mem_univ i)).symm
      _ = _ := by rw [heraseS]; simp [columnS]
  have hsumU :
      (∑ j, ∑ x ∈ columnU j, weight j x) =
        (∑ x ∈ U, weight i x) +
          ∑ j ∈ (Finset.univ : Finset ι).erase i,
            ∑ x ∈ U, weight j x := by
    calc
      (∑ j, ∑ x ∈ columnU j, weight j x) =
          (∑ x ∈ columnU i, weight i x) +
            ∑ j ∈ (Finset.univ : Finset ι).erase i,
              ∑ x ∈ columnU j, weight j x :=
        (Finset.add_sum_erase (Finset.univ : Finset ι)
          (fun j => ∑ x ∈ columnU j, weight j x)
          (Finset.mem_univ i)).symm
      _ = _ := by simp [columnU]
  rw [hsumS] at hzS
  rw [hsumU] at hzU
  linarith

end AffineSectionLogRank
