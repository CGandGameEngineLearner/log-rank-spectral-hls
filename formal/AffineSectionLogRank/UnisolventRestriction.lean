import Mathlib

open scoped BigOperators

namespace AffineSectionLogRank

/-- A subset `Y` is unisolvent for a function subspace `V` when a member of
`V` vanishing on `Y` must vanish everywhere. -/
def IsUnisolvent
    {R Ω : Type*} [Semiring R]
    (V : Submodule R (Ω → R)) (Y : Set Ω) : Prop :=
  ∀ f ∈ V, (∀ y ∈ Y, f y = 0) → f = 0

/-- Unisolvence lifts every finite linear relation observed on the sparse
restriction back to the full ambient domain. -/
theorem linearCombination_eq_zero_of_isUnisolvent
    {R Ω ι : Type*} [CommSemiring R] [Fintype ι]
    (V : Submodule R (Ω → R)) (Y : Set Ω)
    (hY : IsUnisolvent V Y)
    (f : ι → Ω → R) (hf : ∀ i, f i ∈ V) (coeff : ι → R)
    (hzero : ∀ y ∈ Y, ∑ i, coeff i * f i y = 0) :
    (fun x => ∑ i, coeff i * f i x) = 0 := by
  let g : Ω → R := fun x => ∑ i, coeff i * f i x
  have hgV : g ∈ V := by
    dsimp [g]
    have hsum :
        (fun x => ∑ i, coeff i * f i x) = ∑ i, coeff i • f i := by
      funext x
      simp
    rw [hsum]
    apply Submodule.sum_mem
    intro i hi
    exact V.smul_mem (coeff i) (hf i)
  apply hY g hgV
  intro y hy
  exact hzero y hy

/-- Every ambient relation restricts to a relation on any subset. -/
theorem restricted_linearCombination_eq_zero
    {R Ω ι : Type*} [CommSemiring R] [Fintype ι]
    (Y : Set Ω) (f : ι → Ω → R) (coeff : ι → R)
    (hzero : (fun x => ∑ i, coeff i * f i x) = 0) :
    ∀ y ∈ Y, ∑ i, coeff i * f i y = 0 := by
  intro y hy
  have := congrFun hzero y
  simpa using this

/-- Under unisolvence, a finite family has exactly the same coefficient
relations before and after restriction. -/
theorem full_relation_iff_restricted_relation_of_isUnisolvent
    {R Ω ι : Type*} [CommSemiring R] [Fintype ι]
    (V : Submodule R (Ω → R)) (Y : Set Ω)
    (hY : IsUnisolvent V Y)
    (f : ι → Ω → R) (hf : ∀ i, f i ∈ V) (coeff : ι → R) :
    (fun x => ∑ i, coeff i * f i x) = 0 ↔
      ∀ y ∈ Y, ∑ i, coeff i * f i y = 0 := by
  constructor
  · exact restricted_linearCombination_eq_zero Y f coeff
  · exact linearCombination_eq_zero_of_isUnisolvent V Y hY f hf coeff

/-- If `Y` is unisolvent for a space containing `f * (f - 1)`, then being
zero-one valued on `Y` forces `f` to be zero-one valued everywhere.  For a
degree filtration this is applied with the degree-`2s` space. -/
theorem zero_or_one_everywhere_of_isUnisolvent
    {Ω : Type*}
    (V : Submodule ℝ (Ω → ℝ)) (Y : Set Ω)
    (hY : IsUnisolvent V Y) (f : Ω → ℝ)
    (hprod : (fun x => f x * (f x - 1)) ∈ V)
    (hbool : ∀ y ∈ Y, f y = 0 ∨ f y = 1) :
    ∀ x, f x = 0 ∨ f x = 1 := by
  have hzeroY : ∀ y ∈ Y, f y * (f y - 1) = 0 := by
    intro y hy
    rcases hbool y hy with h | h
    · simp [h]
    · simp [h]
  have hzero := hY (fun x => f x * (f x - 1)) hprod hzeroY
  intro x
  have hx := congrFun hzero x
  simp only [Pi.zero_apply] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

end AffineSectionLogRank
