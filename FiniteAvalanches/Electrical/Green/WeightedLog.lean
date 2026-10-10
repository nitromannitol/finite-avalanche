import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.WeightedLog
open scoped BigOperators
noncomputable section

/-- A zero current contributes exactly zero. -/
theorem zero_mul_log_div (θ : ℝ) : (0 : ℝ) * Real.log (θ / 0) = 0 := zero_mul _

/-- `log t ≤ t - 1`, with `t = M / (m p)`, weighted by `p`; valid for every `p ≥ 0`. -/
theorem weighted_log_pointwise {p θ M m : ℝ} (hp : 0 ≤ p) (hθ : 0 < θ) (hM : 0 < M)
    (hm : 0 < m) :
    p * Real.log (θ / p) ≤ p * Real.log (m * θ / M) + M / m - p := by
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0]
    have h : (0 : ℝ) ≤ M / m := by positivity
    simpa using h
  · have hp0 : p ≠ 0 := hpos.ne'
    have hM0 : M ≠ 0 := hM.ne'
    have hm0 : m ≠ 0 := hm.ne'
    have hA : 0 < m * θ / M := by positivity
    have ht : 0 < M / (m * p) := by positivity
    have e : θ / p = (m * θ / M) * (M / (m * p)) := by
      field_simp
    have hsplit : Real.log (θ / p) =
        Real.log (m * θ / M) + Real.log (M / (m * p)) := by
      rw [e, Real.log_mul hA.ne' ht.ne']
    have hle : Real.log (M / (m * p)) ≤ M / (m * p) - 1 :=
      Real.log_le_sub_one_of_pos ht
    have hpt : p * (M / (m * p)) = M / m := by
      field_simp
    have hmul : p * Real.log (M / (m * p)) ≤ p * (M / (m * p) - 1) :=
      mul_le_mul_of_nonneg_left hle hpos.le
    have h2 : p * (M / (m * p) - 1) = M / m - p := by
      rw [mul_sub, hpt, mul_one]
    calc p * Real.log (θ / p)
        = p * Real.log (m * θ / M) + p * Real.log (M / (m * p)) := by
          rw [hsplit]; ring
      _ ≤ p * Real.log (m * θ / M) + p * (M / (m * p) - 1) := by linarith
      _ = p * Real.log (m * θ / M) + M / m - p := by linarith

/-- The weighted logarithm (Jensen) bound for nonnegative weights with total mass `M > 0`;
zero weights are allowed and the original cardinality is kept. -/
theorem sum_mul_log_div_le {I : Type*} [Fintype I] (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    {θ M : ℝ} (hθ : 0 < θ) (hM : 0 < M) (hsum : ∑ i, p i = M) :
    ∑ i, p i * Real.log (θ / p i) ≤ M * Real.log ((Fintype.card I : ℝ) * θ / M) := by
  have hcard : (0 : ℝ) < Fintype.card I := by
    rcases Nat.eq_zero_or_pos (Fintype.card I) with h | h
    · exfalso
      haveI : IsEmpty I := Fintype.card_eq_zero_iff.mp h
      have h0 : ∑ i, p i = 0 := Finset.sum_eq_zero fun i _ => (IsEmpty.false i).elim
      linarith
    · exact_mod_cast h
  have hc0 : (Fintype.card I : ℝ) ≠ 0 := hcard.ne'
  have hpt : ∀ i, p i * Real.log (θ / p i) ≤
      p i * Real.log ((Fintype.card I : ℝ) * θ / M) + M / Fintype.card I - p i :=
    fun i => weighted_log_pointwise (hp i) hθ hM hcard
  have hcm : (Fintype.card I : ℝ) * (M / Fintype.card I) = M := by
    field_simp
  calc ∑ i, p i * Real.log (θ / p i)
      ≤ ∑ i, (p i * Real.log ((Fintype.card I : ℝ) * θ / M) + M / Fintype.card I - p i) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = M * Real.log ((Fintype.card I : ℝ) * θ / M) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hsum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcm]
        ring

/-- The same bound with `M` the actual total mass. -/
theorem sum_mul_log_div_le_of_sum_pos {I : Type*} [Fintype I] (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) {θ : ℝ} (hθ : 0 < θ) (hM : 0 < ∑ i, p i) :
    ∑ i, p i * Real.log (θ / p i) ≤
      (∑ i, p i) * Real.log ((Fintype.card I : ℝ) * θ / ∑ i, p i) :=
  sum_mul_log_div_le p hp hθ hM rfl

/-- The version with `1` added inside both sides. -/
theorem sum_mul_one_add_log_div_le {I : Type*} [Fintype I] (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) {θ M : ℝ} (hθ : 0 < θ) (hM : 0 < M) (hsum : ∑ i, p i = M) :
    ∑ i, p i * (1 + Real.log (θ / p i)) ≤
      M * (1 + Real.log ((Fintype.card I : ℝ) * θ / M)) := by
  have h := sum_mul_log_div_le p hp hθ hM hsum
  have e : ∑ i, p i * (1 + Real.log (θ / p i)) =
      ∑ i, p i + ∑ i, p i * Real.log (θ / p i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, hsum]
  nlinarith [h]

/-- Weighted consumer: a pointwise bound `U i ≤ C (1 + log (θ / p i))` required only at
positive currents, with `C ≥ 0`, gives the weighted sum bound. -/
theorem weighted_sum_le {I : Type*} [Fintype I] (p U : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    {θ C M : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C) (hM : 0 < M) (hsum : ∑ i, p i = M)
    (hU : ∀ i, 0 < p i → U i ≤ C * (1 + Real.log (θ / p i))) :
    ∑ i, p i * U i ≤ C * M * (1 + Real.log ((Fintype.card I : ℝ) * θ / M)) := by
  have hpt : ∀ i, p i * U i ≤ C * (p i * (1 + Real.log (θ / p i))) := by
    intro i
    rcases (hp i).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · have h := mul_le_mul_of_nonneg_left (hU i hpos) hpos.le
      linarith
  have h1 : ∑ i, p i * U i ≤ ∑ i, C * (p i * (1 + Real.log (θ / p i))) :=
    Finset.sum_le_sum fun i _ => hpt i
  have h2 : ∑ i, C * (p i * (1 + Real.log (θ / p i))) =
      C * ∑ i, p i * (1 + Real.log (θ / p i)) := by
    rw [Finset.mul_sum]
  have h3 := sum_mul_one_add_log_div_le p hp hθ hM hsum
  calc ∑ i, p i * U i
      ≤ C * ∑ i, p i * (1 + Real.log (θ / p i)) := h1.trans_eq h2
    _ ≤ C * (M * (1 + Real.log ((Fintype.card I : ℝ) * θ / M))) :=
        mul_le_mul_of_nonneg_left h3 hC
    _ = C * M * (1 + Real.log ((Fintype.card I : ℝ) * θ / M)) := (mul_assoc _ _ _).symm

/-- Adjacent currents on `Fin m`: `U i = W i + W (i + 1)`, as at `main.tex:918–919`. -/
theorem weighted_adjacent_le {m : ℕ} (p : Fin m → ℝ) (W : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    {θ C M : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C) (hM : 0 < M) (hsum : ∑ i, p i = M)
    (hW : ∀ i : Fin m, 0 < p i →
      W (i : ℕ) + W ((i : ℕ) + 1) ≤ C * (1 + Real.log (θ / p i))) :
    ∑ i : Fin m, p i * (W (i : ℕ) + W ((i : ℕ) + 1)) ≤
      C * M * (1 + Real.log ((m : ℝ) * θ / M)) := by
  have h := weighted_sum_le p (fun i : Fin m => W (i : ℕ) + W ((i : ℕ) + 1)) hp hθ hC hM
    hsum hW
  rwa [Fintype.card_fin] at h

/-- The paper's `mθ/M ≥ 1` when every current is at most `θ` (not used by the bounds above). -/
theorem one_le_card_mul_div {I : Type*} [Fintype I] (p : I → ℝ) {θ M : ℝ} (hM : 0 < M)
    (hsum : ∑ i, p i = M) (hθ : ∀ i, p i ≤ θ) :
    1 ≤ (Fintype.card I : ℝ) * θ / M := by
  have h : ∑ i, p i ≤ ∑ _i : I, θ := Finset.sum_le_sum fun i _ => hθ i
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [le_div_iff₀ hM]
  linarith

#print axioms FiniteAvalanches.Electrical.WeightedLog.zero_mul_log_div
#print axioms FiniteAvalanches.Electrical.WeightedLog.weighted_log_pointwise
#print axioms FiniteAvalanches.Electrical.WeightedLog.sum_mul_log_div_le
#print axioms FiniteAvalanches.Electrical.WeightedLog.sum_mul_log_div_le_of_sum_pos
#print axioms FiniteAvalanches.Electrical.WeightedLog.sum_mul_one_add_log_div_le
#print axioms FiniteAvalanches.Electrical.WeightedLog.weighted_sum_le
#print axioms FiniteAvalanches.Electrical.WeightedLog.weighted_adjacent_le
#print axioms FiniteAvalanches.Electrical.WeightedLog.one_le_card_mul_div

end
end FiniteAvalanches.Electrical.WeightedLog
