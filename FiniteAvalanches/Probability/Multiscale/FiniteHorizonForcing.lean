import FiniteAvalanches.Probability.Multiscale.GeometricForcing

/-! Finite-horizon iteration for the current consecutive-scale recurrence.
The numerical continuation after the horizon is homogeneous and is used only
to apply the scalar geometric-forcing lemma. No forest observable is changed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Probability.CurrentRecurrence
noncomputable section

/-- One coefficient bounds every finite-horizon recurrence at its own last stage. -/
theorem geometric_forcing_bound_finite (b : ℕ) (hb : 6 ≤ b) (q D : ℝ)
    (hq : (1 / 2 : ℝ) < q) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℕ → ℝ) (n : ℕ), 1 ≤ n → u 1 ≤ 1 →
      (∀ i : ℕ, 2 ≤ i → i ≤ n → u i ≤ q * u (i - 1) + D / (b : ℝ) ^ i) →
      u n ≤ C * q ^ n := by
  obtain ⟨C, hC, hbound⟩ := geometric_forcing_bound b hb q D hq hD
  refine ⟨C, hC, ?_⟩
  intro u n hn h1 hrec
  let v : ℕ → ℝ := fun i => if i ≤ n then u i else q ^ (i - n) * u n
  have hv1 : v 1 ≤ 1 := by simpa only [v, if_pos hn] using h1
  have hvrec : ∀ i : ℕ, 2 ≤ i → v i ≤ q * v (i - 1) + D / (b : ℝ) ^ i := by
    intro i hi
    by_cases hin : i ≤ n
    · simpa only [v, if_pos hin, if_pos (by omega : i - 1 ≤ n)] using hrec i hi hin
    · have hvstep : v i = q * v (i - 1) := by
        by_cases hprev : i - 1 ≤ n
        · have hip : i = n + 1 := by omega
          subst i
          have hvi : v (n + 1) = q * u n := by
            dsimp only [v]
            rw [if_neg (by omega : ¬n + 1 ≤ n), show n + 1 - n = 1 by omega, pow_one]
          have hvprev : v (n + 1 - 1) = u n := by
            rw [show n + 1 - 1 = n by omega]
            exact if_pos (le_refl n)
          rw [hvi, hvprev]
        · simp only [v, if_neg hin, if_neg hprev]
          rw [show i - n = (i - 1 - n) + 1 by omega, pow_succ]
          ring
      rw [hvstep]
      exact le_add_of_nonneg_right (div_nonneg hD (pow_nonneg (Nat.cast_nonneg _) _))
  have hv := hbound v hv1 hvrec n hn
  simpa only [v, if_pos (le_refl n)] using hv

end
end FiniteAvalanches.Probability.CurrentRecurrence
