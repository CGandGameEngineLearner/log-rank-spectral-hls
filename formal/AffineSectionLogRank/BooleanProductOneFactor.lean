import AffineSectionLogRank.FourPointTwoLevel

namespace AffineSectionLogRank

/-- A Boolean-valued additive function on a Cartesian product cannot have two
nonconstant factors. -/
theorem boolean_additive_two_factor_one_constant
    {X Y : Type*} (c : ℝ) (f : X → ℝ) (g : Y → ℝ)
    (hbool : ∀ x y, realTwoLevel (c + f x + g y)) :
    (∀ x x', f x = f x') ∨ (∀ y y', g y = g y') := by
  by_contra h
  push_neg at h
  obtain ⟨x₀, x₁, hx⟩ := h.1
  obtain ⟨y₀, y₁, hy⟩ := h.2
  let c' := c + f x₀ + g y₀
  let a := f x₁ - f x₀
  let b := g y₁ - g y₀
  have ha : a ≠ 0 := by
    dsimp [a]
    intro hzero
    exact hx (sub_eq_zero.mp hzero).symm
  have hb : b ≠ 0 := by
    dsimp [b]
    intro hzero
    exact hy (sub_eq_zero.mp hzero).symm
  have h₀₀ : realTwoLevel c' := by
    simpa [c', add_assoc] using hbool x₀ y₀
  have h₁₀ : realTwoLevel (c' + a) := by
    have heq : c' + a = c + f x₁ + g y₀ := by
      dsimp [c', a]
      ring
    rw [heq]
    exact hbool x₁ y₀
  have h₀₁ : realTwoLevel (c' + b) := by
    have heq : c' + b = c + f x₀ + g y₁ := by
      dsimp [c', b]
      ring
    rw [heq]
    exact hbool x₀ y₁
  have h₁₁ : realTwoLevel (c' + a + b) := by
    have heq : c' + a + b = c + f x₁ + g y₁ := by
      dsimp [c', a, b]
      ring
    rw [heq]
    exact hbool x₁ y₁
  exact not_all_four_affine_corners_twoLevel c' a b ha hb
    ⟨h₀₀, h₁₀, h₀₁, h₁₁⟩

end AffineSectionLogRank
