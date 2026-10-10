import FiniteAvalanches.Electrical.Green.WeightedLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring

/-! Internal scalar assembly of the theta-free variance bound. The arc and adjacent
bounds are explicit numerical predecessors, not premises of a source theorem. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.VarianceAssembly
open scoped BigOperators

/-- Subtract the constant two before applying the existing weighted-log bound.
Zero currents need no adjacent bound and contribute zero to the sum. -/
theorem variance_le_seven_add_log_of_arc_and_adjacent_bounds {m : ℕ}
    (p : Fin m → ℝ) (W : ℕ → ℝ) {E variance : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hE : 0 < E) (hsum : ∑ i, p i = E)
    (hadj : ∀ i : Fin m, 0 < p i →
      W (i : ℕ) + W ((i : ℕ) + 1) ≤
        2 + 7776 * (1 + Real.log (2 / p i)))
    (harc : variance ≤ E + 3 * ∑ i : Fin m,
      p i * (W (i : ℕ) + W ((i : ℕ) + 1))) :
    variance ≤ 7 * E + 23328 * E * (1 + Real.log ((m : ℝ) * 2 / E)) := by
  have hcenter : ∀ i : Fin m, 0 < p i →
      W (i : ℕ) + W ((i : ℕ) + 1) - 2 ≤
        7776 * (1 + Real.log (2 / p i)) := by
    intro i hi
    linarith only [hadj i hi]
  have hweighted := WeightedLog.weighted_sum_le p
    (fun i : Fin m => W (i : ℕ) + W ((i : ℕ) + 1) - 2) hp
    (θ := 2) (C := 7776) (M := E)
    (by norm_num) (by norm_num) hE hsum hcenter
  simp only [Fintype.card_fin] at hweighted
  have hshift :
      (∑ i : Fin m, p i * (W (i : ℕ) + W ((i : ℕ) + 1) - 2)) =
        (∑ i : Fin m, p i * (W (i : ℕ) + W ((i : ℕ) + 1))) - 2 * E := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
    ring
  rw [hshift] at hweighted
  nlinarith only [harc, hweighted]

/-- Numerical final assembly with the source's explicit universal constant 40000.
This does not establish the arc bound, the split bound, or any Green/current identity. -/
theorem variance_le_40000_of_arc_and_adjacent_bounds {m : ℕ}
    (p : Fin m → ℝ) (W : ℕ → ℝ) {E variance : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp_one : ∀ i, p i ≤ 1)
    (hE : 0 < E) (hsum : ∑ i, p i = E)
    (hadj : ∀ i : Fin m, 0 < p i →
      W (i : ℕ) + W ((i : ℕ) + 1) ≤
        2 + 7776 * (1 + Real.log (2 / p i)))
    (harc : variance ≤ E + 3 * ∑ i : Fin m,
      p i * (W (i : ℕ) + W ((i : ℕ) + 1))) :
    variance ≤ 40000 * E * (1 + Real.log ((m : ℝ) / E)) := by
  have hraw := variance_le_seven_add_log_of_arc_and_adjacent_bounds
    p W hp hE hsum hadj harc
  have hratio : 1 ≤ (m : ℝ) / E := by
    simpa only [Fintype.card_fin, mul_one] using
      (WeightedLog.one_le_card_mul_div p hE hsum hp_one)
  have hratio_pos : 0 < (m : ℝ) / E := zero_lt_one.trans_le hratio
  have hlog_nonneg : 0 ≤ Real.log ((m : ℝ) / E) := Real.log_nonneg hratio
  have hsplit : Real.log ((m : ℝ) * 2 / E) =
      Real.log 2 + Real.log ((m : ℝ) / E) := by
    rw [show (m : ℝ) * 2 / E = 2 * ((m : ℝ) / E) by ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hratio_pos.ne']
  have hlog_two : Real.log (2 : ℝ) ≤ (17 / 24 : ℝ) := by
    calc
      Real.log (2 : ℝ) ≤ 0.6931471808 := Real.log_two_lt_d9.le
      _ ≤ (17 / 24 : ℝ) := by norm_num
  have hconstant : (7 : ℝ) + 23328 * (1 + Real.log 2) ≤ 39859 := by
    linarith only [hlog_two]
  calc
    variance ≤ 7 * E + 23328 * E * (1 + Real.log ((m : ℝ) * 2 / E)) := hraw
    _ = (7 + 23328 * (1 + Real.log 2)) * E +
        23328 * (E * Real.log ((m : ℝ) / E)) := by rw [hsplit]; ring
    _ ≤ 39859 * E + 23328 * (E * Real.log ((m : ℝ) / E)) :=
      add_le_add (mul_le_mul_of_nonneg_right hconstant hE.le) le_rfl
    _ ≤ 40000 * E + 40000 * (E * Real.log ((m : ℝ) / E)) :=
      add_le_add
        (mul_le_mul_of_nonneg_right (by norm_num : (39859 : ℝ) ≤ 40000) hE.le)
        (mul_le_mul_of_nonneg_right (by norm_num : (23328 : ℝ) ≤ 40000)
          (mul_nonneg hE.le hlog_nonneg))
    _ = 40000 * E * (1 + Real.log ((m : ℝ) / E)) := by ring

end FiniteAvalanches.Electrical.VarianceAssembly
