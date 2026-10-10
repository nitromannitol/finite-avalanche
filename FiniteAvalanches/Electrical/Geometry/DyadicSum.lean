module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! Finite dyadic sums with explicit logarithmic constants. -/

@[expose] public section

namespace FiniteAvalanches.Electrical.Geometry

open scoped BigOperators

theorem sum_half_pow_le_two (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) ≤ 2 := by
  have h := geom_sum_mul_neg (1 / 2 : ℝ) n
  have hn : 0 ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) _
  norm_num at h
  linarith only [h, hn]

theorem dyadic_sum_le_cutoff (x : ℝ) (hx : 0 ≤ x) (K n : ℕ)
    (hK : x ≤ (2 : ℝ) ^ K) :
    (∑ k ∈ Finset.range n, min 1 (x / 2 ^ k)) ≤ (K : ℝ) + 2 := by
  have hp : (∑ k ∈ Finset.range K, min 1 (x / 2 ^ k)) ≤ K := by
    calc
      _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => min_le_left _ _
      _ = K := by simp
  have ht : (∑ k ∈ Finset.range n, min 1 (x / 2 ^ (K + k))) ≤ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k _
        apply (min_le_right _ _).trans
        have h := (div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ) < 2) (K+k))).mpr hK
        calc
          x / 2 ^ (K+k) ≤ 2 ^ K / 2 ^ (K+k) := h
          _ = (1 / 2 : ℝ) ^ k := by
            rw [pow_add, div_pow]
            field_simp
            simp only [one_pow]
      _ ≤ 2 := sum_half_pow_le_two n
  calc
    _ ≤ ∑ k ∈ Finset.range (K + n), min 1 (x / 2 ^ k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro k _ _
      exact le_min (by norm_num) (div_nonneg hx (pow_nonneg (by norm_num) _))
    _ = (∑ k ∈ Finset.range K, min 1 (x / 2 ^ k)) +
      ∑ k ∈ Finset.range n, min 1 (x / 2 ^ (K+k)) := Finset.sum_range_add _ _ _
    _ ≤ (K : ℝ) + 2 := add_le_add hp ht

/-- A bound uniform in the finite truncation; the logarithm is the natural logarithm. -/
theorem dyadic_sum_le_log (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.range n, min 1 (x / 2 ^ k)) ≤ 3 + Real.log x / Real.log 2 := by
  obtain ⟨K, hK, hK'⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  have h := dyadic_sum_le_cutoff x (by linarith) (K+1) n hK'.le
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) K) hK
  rw [Real.log_pow] at hlog
  have hKlog : (K : ℝ) ≤ Real.log x / Real.log 2 :=
    (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
  norm_num at h
  linarith only [h, hKlog]

/-- Every scale at least epsilon has a genuine half-open dyadic bin. -/
theorem exists_dyadic_bin (epsilon r : ℝ) (he : 0 < epsilon) (hr : epsilon ≤ r) :
    ∃ k : ℕ, 2 ^ k * epsilon ≤ r ∧ r < 2 ^ (k+1) * epsilon := by
  have hx : 1 ≤ r / epsilon := (le_div_iff₀ he).mpr (by simpa using hr)
  obtain ⟨k, h1, h2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  exact ⟨k, (le_div_iff₀ he).mp h1, (div_lt_iff₀ he).mp h2⟩

end FiniteAvalanches.Electrical.Geometry
