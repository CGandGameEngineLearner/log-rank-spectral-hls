import AffineSectionLogRank.UniformLayerConstantSum

open scoped BigOperators

namespace AffineSectionLogRank

/-- The kernel of evaluation on a complete product of nontrivial uniform
layers has block-constant coordinate coefficients. -/
theorem productLayerKernel_block_constant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (k : ι → ℕ) (weight : ∀ i, α i → ℝ) (constant : ℝ)
    (hkpos : ∀ i, 1 ≤ k i) (hklt : ∀ i, k i < Fintype.card (α i))
    (hzero : ∀ column : (i : ι) → Finset (α i),
      (∀ i, (column i).card = k i) →
      constant + ∑ i, ∑ x ∈ column i, weight i x = 0) :
    ∀ i x y, weight i x = weight i y := by
  classical
  have hkcard (i : ι) :
      k i ≤ (Finset.univ : Finset (α i)).card := by
    simpa using (hklt i).le
  let U (i : ι) : Finset (α i) :=
    Classical.choose (Finset.exists_subset_card_eq (hkcard i))
  have hUcard (i : ι) : (U i).card = k i :=
    (Classical.choose_spec (Finset.exists_subset_card_eq (hkcard i))).2
  intro i
  apply constant_of_sum_eq_on_powersetCard (k i) (weight i)
    (∑ x ∈ U i, weight i x) (hkpos i) (hklt i)
  intro S hScard
  let columnS : (j : ι) → Finset (α j) := fun j =>
    if hji : j = i then hji.symm ▸ S else U j
  let columnU : (j : ι) → Finset (α j) := fun j => U j
  have hcardS : ∀ j, (columnS j).card = k j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [columnS, hScard]
    · simp [columnS, hji, hUcard]
  have hcardU : ∀ j, (columnU j).card = k j := by
    intro j
    simp [columnU, hUcard]
  have hzS := hzero columnS hcardS
  have hzU := hzero columnU hcardU
  have heraseS :
      (∑ j ∈ (Finset.univ : Finset ι).erase i,
        ∑ x ∈ columnS j, weight j x) =
      ∑ j ∈ (Finset.univ : Finset ι).erase i,
        ∑ x ∈ U j, weight j x := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [columnS, hji]
  have hsumS :
      (∑ j, ∑ x ∈ columnS j, weight j x) =
        (∑ x ∈ S, weight i x) +
          ∑ j ∈ (Finset.univ : Finset ι).erase i,
            ∑ x ∈ U j, weight j x := by
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
        (∑ x ∈ U i, weight i x) +
          ∑ j ∈ (Finset.univ : Finset ι).erase i,
            ∑ x ∈ U j, weight j x := by
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
