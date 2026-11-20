import FiniteAvalanches.Support.Plane.ChartOrientation

/-!
# Normalization of interval parameters

An increasing continuous change of parameter can send three prescribed times
to the quarter, half, and three-quarter points.
-/

namespace FiniteAvalanches.Electrical

noncomputable section

private def clipUnit (x : ℝ) : ℝ := max 0 (min x 1)

private theorem clipUnit_mono : Monotone clipUnit := by
  intro x y h
  exact max_le_max le_rfl (min_le_min h le_rfl)

/-- Three ordered interior times can be reached at the three quarter points by
an increasing endpoint-preserving continuous change of parameter. -/
theorem exists_interval_normalization {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c < 1) :
    ∃ ρ : C(unitInterval, unitInterval), StrictMono ρ ∧ ρ 0 = 0 ∧ ρ 1 = 1 ∧
      (ρ ⟨1 / 4, by norm_num⟩ : ℝ) = a ∧
      (ρ ⟨1 / 2, by norm_num⟩ : ℝ) = b ∧
      (ρ ⟨3 / 4, by norm_num⟩ : ℝ) = c := by
  let d := min a (min (b - a) (min (c - b) (1 - c))) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hda : d ≤ a := by dsimp [d]; have := min_le_left a (min (b - a) (min (c - b) (1 - c))); linarith
  have hdb : d ≤ b - a := by dsimp [d]; have := (min_le_right a (min (b - a) (min (c - b) (1 - c)))).trans (min_le_left _ _); linarith
  have hdc : d ≤ c - b := by dsimp [d]; have := (min_le_right a (min (b - a) (min (c - b) (1 - c)))).trans ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hde : d ≤ 1 - c := by dsimp [d]; have := (min_le_right a (min (b - a) (min (c - b) (1 - c)))).trans ((min_le_right _ _).trans (min_le_right _ _)); linarith
  let f : ℝ → ℝ := fun t => 4 * d * t + (a - d) * clipUnit (4 * t) +
    (b - a - d) * clipUnit (4 * t - 1) + (c - b - d) * clipUnit (4 * t - 2) +
    (1 - c - d) * clipUnit (4 * t - 3)
  have hfcont : Continuous f := by
    dsimp [f, clipUnit]
    fun_prop
  have hfmono : StrictMono f := by
    intro x y hxy
    have h₀ := clipUnit_mono (show 4 * x ≤ 4 * y by linarith)
    have h₁ := clipUnit_mono (show 4 * x - 1 ≤ 4 * y - 1 by linarith)
    have h₂ := clipUnit_mono (show 4 * x - 2 ≤ 4 * y - 2 by linarith)
    have h₃ := clipUnit_mono (show 4 * x - 3 ≤ 4 * y - 3 by linarith)
    have h₀' := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hda)
    have h₁' := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hdb)
    have h₂' := mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hdc)
    have h₃' := mul_le_mul_of_nonneg_left h₃ (sub_nonneg.mpr hde)
    change 4 * d * x + _ + _ + _ + _ < 4 * d * y + _ + _ + _ + _
    nlinarith
  have hf0 : f 0 = 0 := by simp [f, clipUnit]
  have hf1 : f 1 = 1 := by norm_num [f, clipUnit]; ring
  have hfquarter : f (1 / 4) = a := by norm_num [f, clipUnit]; ring
  have hfhalf : f (1 / 2) = b := by norm_num [f, clipUnit]; ring
  have hfthreequarter : f (3 / 4) = c := by norm_num [f, clipUnit]; ring
  have hfmem (t : unitInterval) : f t ∈ unitInterval := by
    constructor
    · rw [← hf0]; exact hfmono.monotone t.property.1
    · rw [← hf1]; exact hfmono.monotone t.property.2
  let ρ : C(unitInterval, unitInterval) := ⟨fun t => ⟨f t, hfmem t⟩,
    (hfcont.comp continuous_subtype_val).subtype_mk hfmem⟩
  refine ⟨ρ, ?_, Subtype.ext hf0, Subtype.ext hf1, hfquarter, hfhalf, hfthreequarter⟩
  intro x y h
  exact hfmono h

end
end FiniteAvalanches.Electrical
