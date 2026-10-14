import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Scalar iteration for the consecutive-scale inverse-mean recurrence in
`cd552a5075922522da04d2284b5bff12ee16cbd5`, main.tex lines 525–534.
This module proves only a numerical recurrence estimate. The recurrence for the
actual Wilson forest must be derived separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Probability.CurrentRecurrence

open scoped BigOperators

/-- The explicit geometric-forcing constant is positive and bounds every real
sequence satisfying the scalar recurrence, uniformly over its positive indices.
No sign hypothesis on the sequence or upper bound on `q` is needed. -/
theorem geometric_forcing_bound_explicit
    (b : ℕ) (hb : 6 ≤ b) (q D : ℝ) (hq : (1 / 2 : ℝ) < q) (hD : 0 ≤ D) :
    0 < q⁻¹ + D * (1 / ((b : ℝ) * q)) ^ 2 / (1 - 1 / ((b : ℝ) * q)) ∧
      ∀ u : ℕ → ℝ, u 1 ≤ 1 →
        (∀ i : ℕ, 2 ≤ i → u i ≤ q * u (i - 1) + D / (b : ℝ) ^ i) →
        ∀ n : ℕ, 1 ≤ n →
          u n ≤
            (q⁻¹ + D * (1 / ((b : ℝ) * q)) ^ 2 / (1 - 1 / ((b : ℝ) * q))) * q ^ n := by
  have hbR : (6 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : 0 < (b : ℝ) := lt_of_lt_of_le (by norm_num) hbR
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hbq : 1 < (b : ℝ) * q := by
    calc
      1 < (6 : ℝ) * q := by linarith only [hq]
      _ ≤ (b : ℝ) * q := mul_le_mul_of_nonneg_right hbR hq0.le
  let s : ℝ := 1 / ((b : ℝ) * q)
  have hs0 : 0 < s := one_div_pos.mpr (mul_pos hb0 hq0)
  have hs1 : s < 1 := by
    dsimp only [s]
    apply (div_lt_iff₀ (mul_pos hb0 hq0)).mpr
    simpa only [one_mul] using hbq
  have hden : 0 < 1 - s := sub_pos.mpr hs1
  change 0 < q⁻¹ + D * s ^ 2 / (1 - s) ∧
    ∀ u : ℕ → ℝ, u 1 ≤ 1 →
      (∀ i : ℕ, 2 ≤ i → u i ≤ q * u (i - 1) + D / (b : ℝ) ^ i) →
      ∀ n : ℕ, 1 ≤ n → u n ≤ (q⁻¹ + D * s ^ 2 / (1 - s)) * q ^ n
  constructor
  · exact add_pos_of_pos_of_nonneg (inv_pos.mpr hq0)
      (div_nonneg (mul_nonneg hD (pow_nonneg hs0.le 2)) hden.le)
  · intro u hu hrec
    have hnormalized : ∀ k : ℕ,
        u (k + 1) / q ^ (k + 1) ≤
          q⁻¹ + D * ∑ i ∈ Finset.Ico 2 (k + 2), s ^ i := by
      intro k
      induction k with
      | zero =>
        simpa only [Nat.zero_add, pow_one, Finset.Ico_self, Finset.sum_empty,
          mul_zero, add_zero, one_div] using div_le_div_of_nonneg_right hu hq0.le
      | succ k ih =>
        change u (k + 2) / q ^ (k + 2) ≤
          q⁻¹ + D * ∑ i ∈ Finset.Ico 2 (k + 3), s ^ i
        have hsub : k + 2 - 1 = k + 1 := by omega
        have hstep : u (k + 2) ≤ q * u (k + 1) + D / (b : ℝ) ^ (k + 2) := by
          simpa only [hsub] using hrec (k + 2) (by omega)
        have hfirst : q * u (k + 1) / q ^ (k + 2) = u (k + 1) / q ^ (k + 1) := by
          field_simp [pow_succ, ne_of_gt hq0]
          ring
        have hforcing : (D / (b : ℝ) ^ (k + 2)) / q ^ (k + 2) = D * s ^ (k + 2) := by
          dsimp only [s]
          rw [div_pow, one_pow, div_div, ← mul_pow, mul_one_div]
        calc
          u (k + 2) / q ^ (k + 2) ≤
              (q * u (k + 1) + D / (b : ℝ) ^ (k + 2)) / q ^ (k + 2) :=
            div_le_div_of_nonneg_right hstep (pow_nonneg hq0.le _)
          _ = u (k + 1) / q ^ (k + 1) + D * s ^ (k + 2) := by
            rw [add_div, hfirst, hforcing]
          _ ≤ (q⁻¹ + D * ∑ i ∈ Finset.Ico 2 (k + 2), s ^ i) + D * s ^ (k + 2) :=
            add_le_add ih le_rfl
          _ = q⁻¹ + D * ∑ i ∈ Finset.Ico 2 (k + 3), s ^ i := by
            rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ k + 2)]
            ring
    intro n hn
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hbound := hnormalized (n - 1)
    rw [hn'] at hbound
    have hsum : (∑ i ∈ Finset.Ico 2 (n - 1 + 2), s ^ i) ≤ s ^ 2 / (1 - s) :=
      geom_sum_Ico_le_of_lt_one hs0.le hs1
    have hfull : u n / q ^ n ≤ q⁻¹ + D * s ^ 2 / (1 - s) := by
      calc
        u n / q ^ n ≤ q⁻¹ + D * ∑ i ∈ Finset.Ico 2 (n - 1 + 2), s ^ i := hbound
        _ ≤ q⁻¹ + D * (s ^ 2 / (1 - s)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hD)
        _ = q⁻¹ + D * s ^ 2 / (1 - s) := by rw [mul_div_assoc]
    exact (div_le_iff₀ (pow_pos hq0 n)).mp hfull

/-- A positive constant depending only on `b`, `q` and `D` bounds all scalar
recurrence sequences and all positive indices. -/
theorem geometric_forcing_bound
    (b : ℕ) (hb : 6 ≤ b) (q D : ℝ) (hq : (1 / 2 : ℝ) < q) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℕ → ℝ, u 1 ≤ 1 →
        (∀ i : ℕ, 2 ≤ i → u i ≤ q * u (i - 1) + D / (b : ℝ) ^ i) →
        ∀ n : ℕ, 1 ≤ n → u n ≤ C * q ^ n := by
  obtain ⟨hC, hbound⟩ := geometric_forcing_bound_explicit b hb q D hq hD
  exact ⟨q⁻¹ + D * (1 / ((b : ℝ) * q)) ^ 2 / (1 - 1 / ((b : ℝ) * q)), hC, hbound⟩

end FiniteAvalanches.Probability.CurrentRecurrence
