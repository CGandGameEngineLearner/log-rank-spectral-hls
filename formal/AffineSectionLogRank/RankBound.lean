import Mathlib
import Mathlib.Data.Matrix.Rank

open scoped BigOperators

namespace AffineSectionLogRank

def coordinateValue {d : ℕ} (i : Fin d) (A : Finset (Fin d)) : ℝ :=
  if i ∈ A then 1 else 0

def intersectionAffineMatrix {d a : ℕ}
    {X Y : Type*} (rowSet : X → Finset (Fin d))
    (colSet : Y → Finset (Fin d)) : Matrix X Y ℝ :=
  fun x y => ((rowSet x ∩ colSet y).card : ℝ) - a

noncomputable def leftFeatureMatrix {d a : ℕ}
    {X : Type*} (rowSet : X → Finset (Fin d)) :
    Matrix X (Fin (d + 1)) ℝ :=
  fun x q => Fin.cases (-(a : ℝ))
    (fun i => coordinateValue i (rowSet x)) q

noncomputable def rightFeatureMatrix {d : ℕ}
    {Y : Type*} (colSet : Y → Finset (Fin d)) :
    Matrix (Fin (d + 1)) Y ℝ :=
  fun q y => Fin.cases 1
    (fun i => coordinateValue i (colSet y)) q

theorem intersection_card_eq_coordinate_sum {d : ℕ}
    (A B : Finset (Fin d)) :
    ((A ∩ B).card : ℝ) =
      ∑ i : Fin d, coordinateValue i A * coordinateValue i B := by
  classical
  simp [coordinateValue, Finset.inter_comm]

theorem intersectionAffineMatrix_factorization
    {d a : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (rowSet : X → Finset (Fin d)) (colSet : Y → Finset (Fin d)) :
    intersectionAffineMatrix (a := a) rowSet colSet =
      leftFeatureMatrix (a := a) rowSet * rightFeatureMatrix colSet := by
  classical
  ext x y
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [intersectionAffineMatrix, leftFeatureMatrix, rightFeatureMatrix,
    Fin.cases_zero, Fin.cases_succ]
  rw [← intersection_card_eq_coordinate_sum]
  ring

theorem intersectionAffineMatrix_rank_le
    {d a : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (rowSet : X → Finset (Fin d)) (colSet : Y → Finset (Fin d)) :
    (intersectionAffineMatrix (a := a) rowSet colSet).rank ≤ d + 1 := by
  rw [intersectionAffineMatrix_factorization rowSet colSet]
  calc
    (leftFeatureMatrix (a := a) rowSet * rightFeatureMatrix colSet).rank ≤
        (leftFeatureMatrix (a := a) rowSet).rank := Matrix.rank_mul_le_left _ _
    _ ≤ d + 1 := by
      simpa using Matrix.rank_le_card_width (leftFeatureMatrix (a := a) rowSet)

end AffineSectionLogRank
