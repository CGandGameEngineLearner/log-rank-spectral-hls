import Mathlib

open scoped BigOperators

namespace AffineSectionLogRank

/-- If a real weight function has the same sum on every nontrivial uniform
layer, then all coordinate weights are equal.  This is the kernel lemma behind
the rank-sensitive product-Johnson protocol. -/
theorem constant_of_sum_eq_on_powersetCard
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (weight : α → ℝ) (target : ℝ)
    (hkpos : 1 ≤ k) (hklt : k < Fintype.card α)
    (hconst : ∀ S : Finset α, S.card = k →
      ∑ x ∈ S, weight x = target) :
    ∀ x y : α, weight x = weight y := by
  classical
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  · let pair : Finset α := {x, y}
    let available : Finset α := Finset.univ \ pair
    have hpair : pair.card = 2 := by simp [pair, hxy]
    have hpairSub : pair ⊆ (Finset.univ : Finset α) := Finset.subset_univ _
    have havailCard : available.card = Fintype.card α - 2 := by
      dsimp [available]
      rw [Finset.card_sdiff hpairSub, Finset.card_univ, hpair]
    have hkavail : k - 1 ≤ available.card := by
      rw [havailCard]
      omega
    obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hkavail
    have hxU : x ∉ U := by
      intro hx
      have hxAvail := hUsub hx
      exact (Finset.mem_sdiff.mp hxAvail).2 (by simp [pair])
    have hyU : y ∉ U := by
      intro hy
      have hyAvail := hUsub hy
      exact (Finset.mem_sdiff.mp hyAvail).2 (by simp [pair])
    have hSCard : (insert x U).card = k := by
      simp [hxU, hUcard]
      omega
    have hTCard : (insert y U).card = k := by
      simp [hyU, hUcard]
      omega
    have hS := hconst (insert x U) hSCard
    have hT := hconst (insert y U) hTCard
    simp [Finset.sum_insert, hxU, hyU] at hS hT
    linarith

end AffineSectionLogRank
