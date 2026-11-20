import FiniteAvalanches.Support.Plane.SlitCrossingDegree

/-!
# Winding degrees on the two sides of a horizontal crossing

Let a closed loop meet the open vertical segment between `x₀ - a i` and
`x₀ + a i` at most at one time, where it runs horizontally through `x₀` with
an affine parametrization. Its degree around the upper endpoint exceeds its
degree around the lower endpoint by the direction of the crossing: one when it
runs to the right, minus one when it runs to the left, zero when there is no
crossing. The quotient of the two recentered loops crosses the negative real
axis exactly at the crossing time.
-/

namespace FiniteAvalanches.Electrical

open QuantumZipper.CA.Topo
open Complex Set

/-- The degree of a loop around the point above a horizontal crossing exceeds
its degree around the point below by the direction of the crossing. -/
theorem loopDeg_upper_eq_lower_add_of_crossing (β : C(unitInterval, ℂ)) (hc : β 0 = β 1)
    {x₀ a : ℝ} (ha : 0 < a)
    (hup : ∀ t, β t ≠ (x₀ : ℂ) + a * I) (hlow : ∀ t, β t ≠ (x₀ : ℂ) - a * I)
    (σ : ℤ) (hσ : σ = 0 ∨ σ = 1 ∨ σ = -1) (t₀ : unitInterval)
    (hseg : ∀ t, (β t).re = x₀ → |(β t).im| < a → σ ≠ 0 ∧ t = t₀)
    (hloc : σ ≠ 0 → 0 < (t₀ : ℝ) ∧ (t₀ : ℝ) < 1 ∧ ∃ ε > 0, ∃ κ > 0, ∀ t : unitInterval,
      |(t : ℝ) - t₀| < ε → β t = ((x₀ + σ * κ * ((t : ℝ) - t₀) : ℝ) : ℂ)) :
    loopDeg (β - ContinuousMap.const unitInterval ((x₀ : ℂ) + a * I))
        (fun t => sub_ne_zero.mpr (hup t)) =
      loopDeg (β - ContinuousMap.const unitInterval ((x₀ : ℂ) - a * I))
        (fun t => sub_ne_zero.mpr (hlow t)) + σ := by
  set wup : ℂ := (x₀ : ℂ) + a * I with hwup
  set wlow : ℂ := (x₀ : ℂ) - a * I with hwlow
  have hnelow : ∀ t, β t - wlow ≠ 0 := fun t => sub_ne_zero.mpr (hlow t)
  have hneup : ∀ t, β t - wup ≠ 0 := fun t => sub_ne_zero.mpr (hup t)
  let δ : C(unitInterval, ℂ) := ⟨fun t => (β t - wup) / (β t - wlow),
    (β.continuous.sub continuous_const).div (β.continuous.sub continuous_const) hnelow⟩
  have hδ : ∀ t, δ t ≠ 0 := fun t => div_ne_zero (hneup t) (hnelow t)
  have hδc : δ 0 = δ 1 := by simp [δ, hc]
  have hprod : β - ContinuousMap.const unitInterval wup =
      (β - ContinuousMap.const unitInterval wlow) * δ := by
    ext t
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply, δ,
      ContinuousMap.coe_mk]
    field_simp [hnelow t]
  have hmul := loopDeg_mul (β - ContinuousMap.const unitInterval wlow) δ (fun t => hnelow t) hδ
    (by simp [hc]) hδc
  rw [loopDeg_congr hprod _ (fun t => by simpa using mul_ne_zero (hnelow t) (hδ t)), hmul]
  congr 1
  have hN : ∀ t, 0 < ((β t).re - x₀) ^ 2 + ((β t).im + a) ^ 2 := by
    intro t
    by_contra hle
    have h1 : (β t).re - x₀ = 0 := by nlinarith [sq_nonneg ((β t).re - x₀), sq_nonneg ((β t).im + a)]
    have h2 : (β t).im + a = 0 := by nlinarith [sq_nonneg ((β t).re - x₀), sq_nonneg ((β t).im + a)]
    apply hlow t
    apply Complex.ext <;> simp [wlow] <;> linarith
  have hzr : ∀ t, (β t - wup).re = (β t).re - x₀ := fun t => by simp [wup]
  have hzi : ∀ t, (β t - wup).im = (β t).im - a := fun t => by simp [wup]
  have hwr : ∀ t, (β t - wlow).re = (β t).re - x₀ := fun t => by simp [wlow]
  have hwi : ∀ t, (β t - wlow).im = (β t).im + a := fun t => by simp [wlow]
  have hδre : ∀ t, (δ t).re = (((β t).re - x₀) ^ 2 + (β t).im ^ 2 - a ^ 2) /
      (((β t).re - x₀) ^ 2 + ((β t).im + a) ^ 2) := by
    intro t
    change ((β t - wup) / (β t - wlow)).re = _
    rw [Complex.div_re, Complex.normSq_apply, hzr, hzi, hwr, hwi, ← add_div]
    congr 1 <;> ring
  have hδim : ∀ t, (δ t).im = -(2 * a * ((β t).re - x₀)) /
      (((β t).re - x₀) ^ 2 + ((β t).im + a) ^ 2) := by
    intro t
    change ((β t - wup) / (β t - wlow)).im = _
    rw [Complex.div_im, Complex.normSq_apply, hzr, hzi, hwr, hwi, ← sub_div]
    congr 1 <;> ring
  have hslit : ∀ t, ¬ (σ ≠ 0 ∧ t = t₀) → δ t ∈ slitPlane := by
    intro t ht
    rw [mem_slitPlane_iff]
    by_contra hnot
    push Not at hnot
    obtain ⟨hre, him⟩ := hnot
    have hn := hN t
    rw [hδim, div_eq_zero_iff, neg_eq_zero] at him
    have hu : (β t).re - x₀ = 0 := by
      rcases him with h | h
      · rcases mul_eq_zero.mp h with h | h
        · linarith
        · exact h
      · linarith
    rw [hδre, hu] at hre
    have hv : (β t).im ^ 2 ≤ a ^ 2 := by
      have := div_nonpos_iff.mp hre
      rcases this with ⟨_, h⟩ | ⟨h1, h2⟩
      · rw [hu] at hn; nlinarith
      · nlinarith
    have hvlt : |(β t).im| < a := by
      have hv' : |(β t).im| ≤ a := by
        have := sq_le_sq.mp hv
        rwa [abs_of_pos ha] at this
      rcases lt_or_eq_of_le hv' with h | h
      · exact h
      · rcases abs_eq ha.le |>.mp h with h' | h'
        · exact absurd (Complex.ext (by simp [wup]; linarith) (by simp [wup, h'])) (hup t)
        · exact absurd (Complex.ext (by simp [wlow]; linarith) (by simp [wlow, h'])) (hlow t)
    exact ht (hseg t (by linarith) hvlt)
  rcases hσ with rfl | rfl | rfl
  · exact loopDeg_eq_zero_of_mem_slitPlane δ hδ hδc (fun t => hslit t (by simp))
  · obtain ⟨h0, h1, ε, hε, κ, hκ, hβ⟩ := hloc (by norm_num)
    have hβre : ∀ t : unitInterval, |(t : ℝ) - t₀| < ε →
        (β t).re - x₀ = κ * ((t : ℝ) - t₀) ∧ (β t).im = 0 := by
      intro t ht
      rw [hβ t ht]
      simp
    have hβ₀ := hβre t₀ (by simpa using hε)
    apply loopDeg_eq_one_of_slit_crossing δ hδ hδc t₀ h0 h1
      (fun t ht => hslit t (fun h => ht h.2)) _ _ hε
    · intro t ht1 ht2
      obtain ⟨hu, hv⟩ := hβre t (by rw [abs_lt]; constructor <;> linarith)
      rw [hδim]
      apply div_pos _ (hN t)
      rw [hu]
      nlinarith [mul_pos (mul_pos ha hκ) (sub_pos.mpr ht2)]
    · intro t ht1 ht2
      obtain ⟨hu, hv⟩ := hβre t (by rw [abs_lt]; constructor <;> linarith)
      rw [hδim]
      apply div_neg_of_neg_of_pos _ (hN t)
      rw [hu]
      nlinarith [mul_pos (mul_pos ha hκ) (sub_pos.mpr ht1)]
    · rw [hδre, hβ₀.1, hβ₀.2]
      simp only [sub_self, mul_zero]
      have : (0 : ℝ) ^ 2 + 0 ^ 2 - a ^ 2 < 0 := by nlinarith
      exact div_neg_of_neg_of_pos this (by nlinarith)
    · rw [hδim, hβ₀.1]
      simp
  · obtain ⟨h0, h1, ε, hε, κ, hκ, hβ⟩ := hloc (by norm_num)
    have hβre : ∀ t : unitInterval, |(t : ℝ) - t₀| < ε →
        (β t).re - x₀ = -(κ * ((t : ℝ) - t₀)) ∧ (β t).im = 0 := by
      intro t ht
      rw [hβ t ht]
      simp
    have hβ₀ := hβre t₀ (by simpa using hε)
    have h := loopDeg_eq_neg_one_of_slit_crossing δ hδ hδc t₀ h0 h1
      (fun t ht => hslit t (fun h => ht h.2)) ?_ ?_ hε ?_ ?_
    · exact h
    · rw [hδre, hβ₀.1, hβ₀.2]
      simp only [mul_zero, neg_zero, sub_self]
      have : (0 : ℝ) ^ 2 + 0 ^ 2 - a ^ 2 < 0 := by nlinarith
      exact div_neg_of_neg_of_pos this (by nlinarith)
    · rw [hδim, hβ₀.1]
      simp
    · intro t ht1 ht2
      obtain ⟨hu, hv⟩ := hβre t (by rw [abs_lt]; constructor <;> linarith)
      rw [hδim]
      apply div_neg_of_neg_of_pos _ (hN t)
      rw [hu]
      nlinarith [mul_pos (mul_pos ha hκ) (sub_pos.mpr ht2)]
    · intro t ht1 ht2
      obtain ⟨hu, hv⟩ := hβre t (by rw [abs_lt]; constructor <;> linarith)
      rw [hδim]
      apply div_pos _ (hN t)
      rw [hu]
      nlinarith [mul_pos (mul_pos ha hκ) (sub_pos.mpr ht1)]

end FiniteAvalanches.Electrical
