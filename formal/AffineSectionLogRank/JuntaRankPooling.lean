import Mathlib

open scoped BigOperators

namespace AffineSectionLogRank

/-- A function depends only on the observations indexed by `S`. -/
def DependsOn
    {X ι R : Type*} (observe : X → ι → Bool) (f : X → R)
    (S : Finset ι) : Prop :=
  ∀ x y, (∀ i ∈ S, observe x i = observe y i) → f x = f y

/-- Dependence is monotone in the allowed observation set. -/
theorem DependsOn.mono
    {X ι R : Type*} {observe : X → ι → Bool} {f : X → R}
    {S T : Finset ι} (hf : DependsOn observe f S) (hST : S ⊆ T) :
    DependsOn observe f T := by
  intro x y hxy
  apply hf x y
  intro i hi
  exact hxy i (hST hi)

/-- A finite linear combination depends only on the union of the supports of
its summands.  This is the formal rank-pooling core used by the low-degree
cube and slice communication theorem. -/
theorem dependsOn_linearCombination_biUnion
    {X ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (observe : X → ι → Bool)
    (f : κ → X → ℝ) (support : κ → Finset ι) (coeff : κ → ℝ)
    (hf : ∀ j, DependsOn observe (f j) (support j)) :
    DependsOn observe
      (fun x => ∑ j, coeff j * f j x)
      ((Finset.univ : Finset κ).biUnion support) := by
  intro x y hxy
  apply Finset.sum_congr rfl
  intro j hj
  have hfj : f j x = f j y := by
    apply hf j x y
    intro i hi
    apply hxy i
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hi⟩
  rw [hfj]

/-- A row represented by a finite basis combination inherits dependence on
the union of the basis supports. -/
theorem dependsOn_of_eq_linearCombination
    {X ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (observe : X → ι → Bool)
    (f : κ → X → ℝ) (support : κ → Finset ι) (coeff : κ → ℝ)
    (row : X → ℝ)
    (hf : ∀ j, DependsOn observe (f j) (support j))
    (hrow : ∀ x, row x = ∑ j, coeff j * f j x) :
    DependsOn observe row ((Finset.univ : Finset κ).biUnion support) := by
  intro x y hxy
  rw [hrow x, hrow y]
  exact dependsOn_linearCombination_biUnion observe f support coeff hf x y hxy

/-- If every basis support has size at most `J`, their common pool has size at
most `J` times the number of basis functions. -/
theorem card_biUnion_support_le
    {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (support : κ → Finset ι) (J : ℕ)
    (hcard : ∀ j, (support j).card ≤ J) :
    ((Finset.univ : Finset κ).biUnion support).card ≤
      Fintype.card κ * J := by
  simpa using
    Finset.card_biUnion_le_card_mul (Finset.univ : Finset κ) support J
      (fun j _ => hcard j)

end AffineSectionLogRank
