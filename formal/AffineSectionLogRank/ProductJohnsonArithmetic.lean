import Mathlib

open scoped BigOperators

namespace AffineSectionLogRank

def localMinority (n s : ℕ) : ℕ := min s (n - s)

def productMinorityCost {ι : Type*} [Fintype ι]
    (n : ℕ) (size : ι → ℕ) : ℕ :=
  ∑ i, localMinority n (size i)

def productJohnsonEnergy {ι : Type*} [Fintype ι]
    (n : ℕ) (size : ι → ℕ) : ℕ :=
  ∑ i, size i * (n - size i)

theorem local_energy_eq_minority_energy
    (n s : ℕ) (hs : s ≤ n) :
    s * (n - s) = localMinority n s * (n - localMinority n s) := by
  unfold localMinority
  by_cases h : s ≤ n - s
  · simp [Nat.min_eq_left h]
  · have h' : n - s ≤ s := by omega
    simp [Nat.min_eq_right h', Nat.sub_sub_self hs, Nat.mul_comm]

theorem local_energy_ge_two_errors
    (n s : ℕ) (hn : 4 ≤ n) (hs : s ≤ n)
    (hminor : 2 ≤ localMinority n s) :
    2 * (n - 2) ≤ s * (n - s) := by
  let h := localMinority n s
  have hcomp : h ≤ n - h := by
    unfold h localMinority
    by_cases hle : s ≤ n - s
    · simp [hle]
    · have hle' : n - s ≤ s := by omega
      simp [hle', Nat.sub_sub_self hs]
  have hh : 2 ≤ h := hminor
  have hhc : 2 ≤ n - h := hh.trans hcomp
  have hx : h = (h - 2) + 2 := by omega
  have hy : n - h = (n - h - 2) + 2 := by omega
  have hn_split : n = h + (n - h) := by omega
  have hn2 : n - 2 = (h - 2) + (n - h - 2) + 2 := by omega
  have hnon : 0 ≤ (h - 2) * (n - h - 2) := Nat.zero_le _
  rw [local_energy_eq_minority_energy n s hs]
  change 2 * (n - 2) ≤ h * (n - h)
  calc
    2 * (n - 2) = 2 * ((h - 2) + (n - h - 2) + 2) := by rw [hn2]
    _ ≤ ((h - 2) + 2) * ((n - h - 2) + 2) := by nlinarith
    _ = h * (n - h) := by rw [← hx, ← hy]

theorem local_energy_ge_of_minority_le_one
    (n s : ℕ) (hs : s ≤ n)
    (hminor : localMinority n s ≤ 1) :
    (n - 1) * localMinority n s ≤ s * (n - s) := by
  rw [local_energy_eq_minority_energy n s hs]
  have hcases : localMinority n s = 0 ∨ localMinority n s = 1 := by omega
  rcases hcases with hzero | hone
  · simp [hzero]
  · simp [hone]

theorem product_energy_ge_of_two_le_minority
    {ι : Type*} [Fintype ι]
    (n : ℕ) (size : ι → ℕ)
    (hn : 4 ≤ n) (hsize : ∀ i, size i ≤ n)
    (htotal : 2 ≤ productMinorityCost n size) :
    2 * (n - 2) ≤ productJohnsonEnergy n size := by
  classical
  by_cases hex : ∃ i, 2 ≤ localMinority n (size i)
  · obtain ⟨i, hi⟩ := hex
    calc
      2 * (n - 2) ≤ size i * (n - size i) :=
        local_energy_ge_two_errors n (size i) hn (hsize i) hi
      _ ≤ ∑ j, size j * (n - size j) := by
        have hsingle := Finset.single_le_sum
          (s := (Finset.univ : Finset ι))
          (f := fun j => size j * (n - size j))
          (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
        simpa using hsingle
  · have hall : ∀ i, localMinority n (size i) ≤ 1 := by
      intro i
      have := not_exists.mp hex i
      omega
    calc
      2 * (n - 2) ≤ (n - 1) * 2 := by omega
      _ ≤ (n - 1) * productMinorityCost n size :=
        Nat.mul_le_mul_left _ htotal
      _ = ∑ i, (n - 1) * localMinority n (size i) := by
        simp [productMinorityCost, Finset.mul_sum]
      _ ≤ ∑ i, size i * (n - size i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact local_energy_ge_of_minority_le_one n (size i) (hsize i) (hall i)

noncomputable def productJohnsonVariance {ι : Type*} [Fintype ι]
    (n : ℕ) (size : ι → ℕ) : ℝ :=
  (productJohnsonEnergy n size : ℝ) / ((4 : ℝ) * ((n - 1 : ℕ) : ℝ))

/-- If a row differs from every block union in at least two coordinates, its
exact product-middle-layer variance is strictly larger than `1/4`. -/
theorem quarter_lt_productJohnsonVariance_of_two_le_minority
    {ι : Type*} [Fintype ι]
    (n : ℕ) (size : ι → ℕ)
    (hn : 4 ≤ n) (hsize : ∀ i, size i ≤ n)
    (htotal : 2 ≤ productMinorityCost n size) :
    (1 : ℝ) / 4 < productJohnsonVariance n size := by
  have henergy := product_energy_ge_of_two_le_minority n size hn hsize htotal
  have hstrict : n - 1 < 2 * (n - 2) := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) < (productJohnsonEnergy n size : ℝ) := by
    exact_mod_cast hstrict.trans_le henergy
  have hn1 : 0 < n - 1 := by omega
  have hden : (0 : ℝ) < (4 : ℝ) * ((n - 1 : ℕ) : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr hn1)
  unfold productJohnsonVariance
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hden]
  norm_num
  nlinarith

end AffineSectionLogRank
