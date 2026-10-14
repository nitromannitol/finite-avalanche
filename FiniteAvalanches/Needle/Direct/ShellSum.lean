import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The logarithmic shell sum for a lattice test function. -/

namespace FiniteAvalanches.Needle
open scoped BigOperators

private theorem shifted_inverse_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 2)) =
      (harmonic (n + 1) : ℝ) - 1 := by
  rw [harmonic, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  rw [Finset.sum_range_succ']
  simp only [zero_add, inv_one, Nat.cast_add, Nat.cast_one, one_div]
  ring_nf

/-- Summing the radial shell weights costs at most a logarithm. -/
theorem needle_shell_sum_le_log (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) / (((k : ℝ) + 2) ^ 2)) ≤
      Real.log ((n : ℝ) + 1) := by
  have hterm (k : ℕ) : ((k : ℝ) + 1) / (((k : ℝ) + 2) ^ 2) ≤
      (1 : ℝ) / ((k : ℝ) + 2) := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    apply (div_le_div_iff₀ (by positivity : 0 < ((k : ℝ) + 2) ^ 2)
      (by positivity : 0 < (k : ℝ) + 2)).mpr
    nlinarith
  calc
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 2) :=
      Finset.sum_le_sum fun k _ => hterm k
    _ = (harmonic (n + 1) : ℝ) - 1 := shifted_inverse_sum n
    _ ≤ Real.log ((n : ℝ) + 1) := by
      have hh := harmonic_le_one_add_log (n + 1)
      simp only [Nat.cast_add, Nat.cast_one] at hh
      linarith

end FiniteAvalanches.Needle
