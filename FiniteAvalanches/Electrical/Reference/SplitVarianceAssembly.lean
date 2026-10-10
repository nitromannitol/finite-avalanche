import FiniteAvalanches.Electrical.Reference.WeightedEntropy

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Reference
open scoped BigOperators

/-- Absorb the adjacent split bounds into the mean-based logarithmic variance
estimate. Zero probabilities remain in both finite sums. -/
theorem split_arc_variance_le {m : ℕ} (p : Fin m → ℝ) (W : Fin (m + 1) → ℝ)
    (variance : ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hmean : 0 < ∑ i, p i) (hw0 : W 0 = 0) (hwm : W (Fin.last m) = 0)
    (hsplit : ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      ∀ j : Fin m, (j.val + 1 = i.val ∨ j.val = i.val) →
        W i ≤ 1 + 3888 * (1 + Real.log (2 / p j)))
    (hvariance : variance ≤ (∑ i, p i) + 3 * ∑ i, p i * (W i.castSucc + W i.succ)) :
    variance ≤ 40000 * (∑ i, p i) * (1 + Real.log ((m : ℝ) / (∑ i, p i))) := by
  have hlog (i : Fin m) : 0 ≤ Real.log (2 / p i) := by
    by_cases hz : p i = 0
    · simp only [hz, div_zero, Real.log_zero, le_refl]
    · have hpos : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm hz)
      apply Real.log_nonneg
      apply (le_div_iff₀ hpos).mpr
      linarith only [hp1 i]
  have hB (i : Fin m) : 0 ≤ 1 + 3888 * (1 + Real.log (2 / p i)) := by
    linarith only [hlog i]
  have hleft (i : Fin m) : W i.castSucc ≤ 1 + 3888 * (1 + Real.log (2 / p i)) := by
    by_cases hz : i.val = 0
    · have hi : i.castSucc = 0 := Fin.ext hz
      rw [hi, hw0]
      exact hB i
    · exact hsplit i.castSucc (by change 0 < i.val; omega) i.isLt i (Or.inr rfl)
  have hright (i : Fin m) : W i.succ ≤ 1 + 3888 * (1 + Real.log (2 / p i)) := by
    by_cases hz : i.val + 1 = m
    · have hi : i.succ = Fin.last m := Fin.ext hz
      rw [hi, hwm]
      exact hB i
    · exact hsplit i.succ (by change 0 < i.val + 1; omega)
        (by change i.val + 1 < m; omega) i (Or.inl rfl)
  have hsum : (∑ i, p i * (W i.castSucc + W i.succ)) ≤
      2 * (∑ i, p i) + 7776 * ((∑ i, p i) + ∑ i, p i * Real.log (2 / p i)) := by
    calc
      _ ≤ ∑ i, p i * (2 + 7776 * (1 + Real.log (2 / p i))) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hp0 i)
        linarith only [hleft i, hright i]
      _ = ∑ i, (2 * p i + 7776 * p i + 7776 * (p i * Real.log (2 / p i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  have hent := weighted_log_two_div_le p hp0 hmean
  have hmR : 0 < (m : ℝ) := by
    have hm : 0 < m := by
      by_contra hn
      have hz : m = 0 := by omega
      subst m
      simp only [Finset.univ_eq_empty, Finset.sum_empty, lt_self_iff_false] at hmean
    exact Nat.cast_pos.mpr hm
  have hlogid : Real.log (2 * (m : ℝ) / (∑ i, p i)) =
      Real.log 2 + Real.log ((m : ℝ) / (∑ i, p i)) := by
    rw [Real.log_div (mul_ne_zero (by norm_num) hmR.ne') hmean.ne',
      Real.log_mul (by norm_num) hmR.ne', Real.log_div hmR.ne' hmean.ne']
    ring
  rw [hlogid] at hent
  have hmass : (∑ i, p i) ≤ (m : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hp1 i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
  have hL : 0 ≤ Real.log ((m : ℝ) / (∑ i, p i)) :=
    Real.log_nonneg ((le_div_iff₀ hmean).mpr (by simpa only [one_mul] using hmass))
  calc
    variance ≤ 7 * (∑ i, p i) + 23328 * (∑ i, p i) *
        (1 + Real.log 2 + Real.log ((m : ℝ) / (∑ i, p i))) := by
      linarith only [hvariance, hsum, hent]
    _ ≤ _ := reference_variance_constant _ _ hmean.le hL

end FiniteAvalanches.Electrical.Reference
