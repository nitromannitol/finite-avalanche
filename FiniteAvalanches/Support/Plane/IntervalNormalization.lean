import FiniteAvalanches.Support.Plane.ChartOrientation

/-!
# Normalization of interval parameters

An increasing continuous change of parameter can send three prescribed times
to the quarter, half, and three-quarter points.
-/

namespace FiniteAvalanches.Electrical

open QuantumZipper.CA.Topo

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

/-- The local winding jump is independent of the location and duration of
its parameter interval. -/
theorem loopDeg_sub_const_sub_eq_one_of_crossing_interval
    (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1) {a : ℝ} (ha : 0 < a)
    (hp : ∀ t, γ t ≠ (a : ℂ)) (hm : ∀ t, γ t ≠ -(a : ℂ))
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hw : w < 1)
    (hfar : ∀ t : unitInterval, (t : ℝ) < u ∨ w < (t : ℝ) →
      a ^ 2 < (γ t).re ^ 2 + (γ t).im ^ 2)
    (hpos : ∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → 0 < (γ t).im)
    (hneg : ∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → (γ t).im < 0)
    (hmid : ∀ t : unitInterval, (t : ℝ) = v → (γ t).re ^ 2 + (γ t).im ^ 2 < a ^ 2) :
    loopDeg (γ - ContinuousMap.const unitInterval (a : ℂ))
        (fun t => sub_ne_zero.mpr (hp t)) -
      loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ)))
        (fun t => sub_ne_zero.mpr (hm t)) = 1 := by
  obtain ⟨ρ, hρ, hρ0, hρ1, hρu, hρv, hρw⟩ :=
    exists_interval_normalization hu huv hvw hw
  let u₀ : unitInterval := ⟨1 / 4, by norm_num⟩
  let v₀ : unitInterval := ⟨1 / 2, by norm_num⟩
  let w₀ : unitInterval := ⟨3 / 4, by norm_num⟩
  have hresult := loopDeg_sub_const_sub_eq_one_of_local_crossing (γ.comp ρ)
    (by change γ (ρ 0) = γ (ρ 1); rw [hρ0, hρ1, hclosed]) ha
    (fun t => hp (ρ t)) (fun t => hm (ρ t))
    (by
      intro t ht
      apply hfar (ρ t)
      rcases ht with ht | ht
      · left
        have hh := hρ (show t < u₀ from ht)
        change (ρ t : ℝ) < (ρ u₀ : ℝ) at hh
        simpa only [u₀, hρu] using hh
      · right
        have hh := hρ (show w₀ < t from ht)
        change (ρ w₀ : ℝ) < (ρ t : ℝ) at hh
        simpa only [w₀, hρw] using hh)
    (by
      intro t hlo hhi
      apply hpos (ρ t)
      · have hh := hρ.monotone (show u₀ ≤ t from hlo)
        change (ρ u₀ : ℝ) ≤ (ρ t : ℝ) at hh
        simpa only [u₀, hρu] using hh
      · have hh := hρ (show t < v₀ from hhi)
        change (ρ t : ℝ) < (ρ v₀ : ℝ) at hh
        simpa only [v₀, hρv] using hh)
    (by
      intro t hlo hhi
      apply hneg (ρ t)
      · have hh := hρ (show v₀ < t from hlo)
        change (ρ v₀ : ℝ) < (ρ t : ℝ) at hh
        simpa only [v₀, hρv] using hh
      · have hh := hρ.monotone (show t ≤ w₀ from hhi)
        change (ρ t : ℝ) ≤ (ρ w₀ : ℝ) at hh
        simpa only [w₀, hρw] using hh)
    (by
      intro t ht
      apply hmid (ρ t)
      have ht' : t = v₀ := Subtype.ext ht
      subst t
      exact hρv)
  have hdp := loopDeg_comp_of_endpoints (γ - ContinuousMap.const unitInterval (a : ℂ))
    (fun t => sub_ne_zero.mpr (hp t)) (by simp only [ContinuousMap.sub_apply,
      ContinuousMap.const_apply, hclosed]) ρ hρ0 hρ1
  have hdm := loopDeg_comp_of_endpoints (γ - ContinuousMap.const unitInterval (-(a : ℂ)))
    (fun t => sub_ne_zero.mpr (hm t)) (by simp only [ContinuousMap.sub_apply,
      ContinuousMap.const_apply, hclosed]) ρ hρ0 hρ1
  have hdp' : loopDeg (γ.comp ρ - ContinuousMap.const unitInterval (a : ℂ))
      (fun t => sub_ne_zero.mpr (hp (ρ t))) =
      loopDeg (γ - ContinuousMap.const unitInterval (a : ℂ))
        (fun t => sub_ne_zero.mpr (hp t)) := by
    convert hdp using 1
    congr 1
  have hdm' : loopDeg (γ.comp ρ - ContinuousMap.const unitInterval (-(a : ℂ)))
      (fun t => sub_ne_zero.mpr (hm (ρ t))) =
      loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ)))
        (fun t => sub_ne_zero.mpr (hm t)) := by
    convert hdm using 1
    congr 1
  rw [← hdp', ← hdm']
  exact hresult

/-- A closed loop crossing the origin once, with opposite local half-plane
orientations, has a unit winding jump across sufficiently close real points. -/
theorem exists_winding_jump_of_local_crossing
    (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    {ε : ℝ} (hε : 0 < ε)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hw : w < 1)
    (hzero : ∀ t : unitInterval, γ t = 0 ↔ (t : ℝ) = v)
    (hpos : ∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → 0 < (γ t).im)
    (hneg : ∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → (γ t).im < 0) :
    ∃ (a : ℝ) (_ : 0 < a) (_ : a < ε) (hp : ∀ t, γ t ≠ (a : ℂ))
        (hm : ∀ t, γ t ≠ -(a : ℂ)),
      loopDeg (γ - ContinuousMap.const unitInterval (a : ℂ))
          (fun t => sub_ne_zero.mpr (hp t)) -
        loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ)))
          (fun t => sub_ne_zero.mpr (hm t)) = 1 := by
  let S : Set unitInterval := {t | (t : ℝ) ≤ u ∨ w ≤ (t : ℝ)}
  have hSclosed : IsClosed S :=
    (isClosed_le continuous_subtype_val continuous_const).union
      (isClosed_le continuous_const continuous_subtype_val)
  have hScompact : IsCompact S := isCompact_univ.of_isClosed_subset hSclosed (Set.subset_univ _)
  have hSnonempty : S.Nonempty := ⟨0, Or.inl (by simpa using le_of_lt hu)⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hScompact.exists_isMinOn hSnonempty
    (γ.continuous.norm.continuousOn)
  have h₀ : γ t₀ ≠ 0 := by
    intro he
    have hv := (hzero t₀).mp he
    rcases ht₀ with ht | ht <;> linarith
  have hr : 0 < ‖γ t₀‖ := norm_pos_iff.mpr h₀
  let a : ℝ := min ‖γ t₀‖ ε / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hae : a < ε := by
    dsimp [a]
    have h := min_le_right ‖γ t₀‖ ε
    linarith
  have har : a < ‖γ t₀‖ := by
    dsimp [a]
    have h := min_le_left ‖γ t₀‖ ε
    linarith
  have hfar : ∀ t : unitInterval, (t : ℝ) ≤ u ∨ w ≤ (t : ℝ) →
      a ^ 2 < (γ t).re ^ 2 + (γ t).im ^ 2 := by
    intro t ht
    have hbound : ‖γ t₀‖ ≤ ‖γ t‖ := hmin ht
    have hn : 0 ≤ ‖γ t‖ := norm_nonneg _
    have hsq : ‖γ t‖ ^ 2 = (γ t).re ^ 2 + (γ t).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith
  have hp : ∀ t, γ t ≠ (a : ℂ) := by
    intro t he
    by_cases hlo : (t : ℝ) ≤ u
    · have h := hfar t (Or.inl hlo)
      rw [he] at h
      simp at h
    by_cases hhi : w ≤ (t : ℝ)
    · have h := hfar t (Or.inr hhi)
      rw [he] at h
      simp at h
    rcases lt_trichotomy (t : ℝ) v with ht | ht | ht
    · have h := hpos t (le_of_not_ge hlo) ht
      rw [he] at h
      simp at h
    · have h := (hzero t).mpr ht
      rw [he] at h
      have : a = 0 := by exact_mod_cast h
      linarith
    · have h := hneg t ht (le_of_not_ge hhi)
      rw [he] at h
      simp at h
  have hm : ∀ t, γ t ≠ -(a : ℂ) := by
    intro t he
    by_cases hlo : (t : ℝ) ≤ u
    · have h := hfar t (Or.inl hlo)
      rw [he] at h
      simp at h
    by_cases hhi : w ≤ (t : ℝ)
    · have h := hfar t (Or.inr hhi)
      rw [he] at h
      simp at h
    rcases lt_trichotomy (t : ℝ) v with ht | ht | ht
    · have h := hpos t (le_of_not_ge hlo) ht
      rw [he] at h
      simp at h
    · have h := (hzero t).mpr ht
      rw [he] at h
      have : a = 0 := by exact_mod_cast (neg_eq_zero.mp h)
      linarith
    · have h := hneg t ht (le_of_not_ge hhi)
      rw [he] at h
      simp at h
  refine ⟨a, ha, hae, hp, hm, ?_⟩
  apply loopDeg_sub_const_sub_eq_one_of_crossing_interval γ hclosed ha hp hm hu huv hvw hw
    (fun t ht => hfar t (ht.imp le_of_lt le_of_lt)) hpos hneg
  intro t ht
  have h := (hzero t).mpr ht
  rw [h]
  simpa using sq_pos_of_pos ha

/-- An orientation-preserving plane chart carries a local winding jump to its
image, preserving the sign of the jump. -/
theorem Source.OrientedChart.exists_winding_jump_of_local_crossing
    (chart : Source.OrientedChart) (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    {ε : ℝ} (hε : 0 < ε)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hw : w < 1)
    (hzero : ∀ t : unitInterval, γ t = 0 ↔ (t : ℝ) = v)
    (hpos : ∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → 0 < (γ t).im)
    (hneg : ∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → (γ t).im < 0) :
    ∃ (a : ℝ) (_ : 0 < a) (_ : a < ε) (hp : ∀ t, γ t ≠ (a : ℂ))
        (hm : ∀ t, γ t ≠ -(a : ℂ)),
      loopDeg (slice (chart.isotopyLoop (a : ℂ) γ) 1)
          (fun t => chart.isotopyLoop_ne_zero (a : ℂ) γ hp (t, 1)) -
        loopDeg (slice (chart.isotopyLoop (-(a : ℂ)) γ) 1)
          (fun t => chart.isotopyLoop_ne_zero (-(a : ℂ)) γ hm (t, 1)) = 1 := by
  obtain ⟨a, ha, hae, hp, hm, hdeg⟩ :=
    FiniteAvalanches.Electrical.exists_winding_jump_of_local_crossing
      γ hclosed hε hu huv hvw hw hzero hpos hneg
  refine ⟨a, ha, hae, hp, hm, ?_⟩
  rw [chart.isotopyLoop_degree (a : ℂ) γ hp hclosed,
    chart.isotopyLoop_degree (-(a : ℂ)) γ hm hclosed]
  exact hdeg

end
end FiniteAvalanches.Electrical
