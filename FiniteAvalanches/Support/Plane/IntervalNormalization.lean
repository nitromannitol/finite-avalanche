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

/-- A crossing in the opposite direction has winding jump minus one. -/
theorem exists_winding_jump_of_reverse_local_crossing
    (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    {ε : ℝ} (hε : 0 < ε)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hw : w < 1)
    (hzero : ∀ t : unitInterval, γ t = 0 ↔ (t : ℝ) = v)
    (hneg : ∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → (γ t).im < 0)
    (hpos : ∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → 0 < (γ t).im) :
    ∃ (a : ℝ) (_ : 0 < a) (_ : a < ε) (hp : ∀ t, γ t ≠ (a : ℂ))
        (hm : ∀ t, γ t ≠ -(a : ℂ)),
      loopDeg (γ - ContinuousMap.const unitInterval (a : ℂ))
          (fun t => sub_ne_zero.mpr (hp t)) -
        loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ)))
          (fun t => sub_ne_zero.mpr (hm t)) = -1 := by
  let δ : C(unitInterval, ℂ) := ⟨fun t => starRingEnd ℂ (γ t),
    Complex.continuous_conj.comp γ.continuous⟩
  have hδclosed : δ 0 = δ 1 := by
    change starRingEnd ℂ (γ 0) = starRingEnd ℂ (γ 1)
    rw [hclosed]
  have hδzero : ∀ t : unitInterval, δ t = 0 ↔ (t : ℝ) = v := by
    intro t
    change starRingEnd ℂ (γ t) = 0 ↔ _
    simpa using hzero t
  obtain ⟨a, ha, hae, hp, hm, hdeg⟩ :=
    exists_winding_jump_of_local_crossing δ hδclosed hε hu huv hvw hw hδzero
      (by intro t ht₁ ht₂; change 0 < -(γ t).im; linarith [hneg t ht₁ ht₂])
      (by intro t ht₁ ht₂; change -(γ t).im < 0; linarith [hpos t ht₁ ht₂])
  have hp' : ∀ t, γ t ≠ (a : ℂ) := by
    intro t h
    apply hp t
    change starRingEnd ℂ (γ t) = _
    rw [h]
    simp only [Complex.conj_ofReal]
  have hm' : ∀ t, γ t ≠ -(a : ℂ) := by
    intro t h
    apply hm t
    change starRingEnd ℂ (γ t) = _
    rw [h]
    simp only [map_neg, Complex.conj_ofReal]
  have hcp := loopDeg_conj (γ - ContinuousMap.const unitInterval (a : ℂ))
    (fun t => sub_ne_zero.mpr (hp' t))
    (by change γ 0 - (a : ℂ) = γ 1 - (a : ℂ); rw [hclosed])
  have hcm := loopDeg_conj (γ - ContinuousMap.const unitInterval (-(a : ℂ)))
    (fun t => sub_ne_zero.mpr (hm' t))
    (by change γ 0 - (-(a : ℂ)) = γ 1 - (-(a : ℂ)); rw [hclosed])
  have hδp : (⟨fun t => starRingEnd ℂ ((γ - ContinuousMap.const unitInterval (a : ℂ)) t),
      Complex.continuous_conj.comp (γ - ContinuousMap.const unitInterval (a : ℂ)).continuous⟩ :
      C(unitInterval, ℂ)) = δ - ContinuousMap.const unitInterval (a : ℂ) := by
    ext t
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, map_sub, Complex.conj_ofReal, δ,
      ContinuousMap.coe_mk]
  have hδm : (⟨fun t => starRingEnd ℂ ((γ - ContinuousMap.const unitInterval (-(a : ℂ))) t),
      Complex.continuous_conj.comp (γ - ContinuousMap.const unitInterval (-(a : ℂ))).continuous⟩ :
      C(unitInterval, ℂ)) = δ - ContinuousMap.const unitInterval (-(a : ℂ)) := by
    ext t
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, map_sub, map_neg, Complex.conj_ofReal, δ,
      ContinuousMap.coe_mk]
  have hcp' : loopDeg (δ - ContinuousMap.const unitInterval (a : ℂ))
      (fun t => sub_ne_zero.mpr (hp t)) =
      -loopDeg (γ - ContinuousMap.const unitInterval (a : ℂ))
        (fun t => sub_ne_zero.mpr (hp' t)) := by simpa only [hδp] using hcp
  have hcm' : loopDeg (δ - ContinuousMap.const unitInterval (-(a : ℂ)))
      (fun t => sub_ne_zero.mpr (hm t)) =
      -loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ)))
        (fun t => sub_ne_zero.mpr (hm' t)) := by simpa only [hδm] using hcm
  refine ⟨a, ha, hae, hp', hm', ?_⟩
  omega

/-- An oriented product-plane chart expressed in complex coordinates. -/
def Source.OrientedChart.complexMap (chart : Source.OrientedChart) : ℂ ≃ₜ ℂ :=
  (Complex.equivRealProdCLM.toHomeomorph.trans chart.map).trans
    Complex.equivRealProdCLM.symm.toHomeomorph

/-- The image of a loop under an oriented chart in complex coordinates. -/
def Source.OrientedChart.complexMapLoop (chart : Source.OrientedChart)
    (γ : C(unitInterval, ℂ)) : C(unitInterval, ℂ) :=
  ⟨fun t => chart.complexMap (γ t), chart.complexMap.continuous.comp γ.continuous⟩

/-- The winding degree of the image loop about the image point equals the
original winding degree. -/
theorem Source.OrientedChart.loopDeg_complexMapLoop_sub_const
    (chart : Source.OrientedChart) (γ : C(unitInterval, ℂ))
    (hclosed : γ 0 = γ 1) (q : ℂ) (hq : ∀ t, γ t ≠ q) :
    loopDeg (chart.complexMapLoop γ - ContinuousMap.const unitInterval (chart.complexMap q))
        (fun t => sub_ne_zero.mpr (fun h => hq t (chart.complexMap.injective h))) =
      loopDeg (γ - ContinuousMap.const unitInterval q) (fun t => sub_ne_zero.mpr (hq t)) := by
  have he : slice (chart.isotopyLoop q γ) 1 =
      chart.complexMapLoop γ - ContinuousMap.const unitInterval (chart.complexMap q) := by
    ext t
    change Complex.equivRealProdCLM.symm
      (chart.isotopy 1 (Complex.equivRealProdCLM (γ t))) -
      Complex.equivRealProdCLM.symm (chart.isotopy 1 (Complex.equivRealProdCLM q)) = _
    rw [show chart.isotopy 1 = chart.map from chart.finish]
    rfl
  simpa only [he] using chart.isotopyLoop_degree q γ hq hclosed

/-- A signed local crossing in chart coordinates gives the same winding jump
for the image loop about the images of its two offset points. -/
theorem Source.OrientedChart.exists_winding_jump_complexMapLoop
    (chart : Source.OrientedChart) (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    {ε : ℝ} (hε : 0 < ε)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hw : w < 1)
    (hzero : ∀ t : unitInterval, γ t = 0 ↔ (t : ℝ) = v)
    (hcross : (∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → 0 < (γ t).im) ∧
        (∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → (γ t).im < 0) ∨
      (∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → (γ t).im < 0) ∧
        (∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → 0 < (γ t).im)) :
    ∃ (a : ℝ) (_ : 0 < a) (_ : a < ε) (hp : ∀ t, γ t ≠ (a : ℂ))
        (hm : ∀ t, γ t ≠ -(a : ℂ)),
      let d := loopDeg (chart.complexMapLoop γ -
          ContinuousMap.const unitInterval (chart.complexMap (a : ℂ)))
        (fun t => sub_ne_zero.mpr (fun h => hp t (chart.complexMap.injective h))) -
        loopDeg (chart.complexMapLoop γ -
          ContinuousMap.const unitInterval (chart.complexMap (-(a : ℂ))))
        (fun t => sub_ne_zero.mpr (fun h => hm t (chart.complexMap.injective h)))
      (d = 1 ∧ (∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → 0 < (γ t).im)) ∨
        (d = -1 ∧ (∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → (γ t).im < 0)) := by
  rcases hcross with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · obtain ⟨a, ha, hae, hp, hm, hd⟩ :=
      FiniteAvalanches.Electrical.exists_winding_jump_of_local_crossing γ hclosed hε hu huv hvw hw
        hzero hpos hneg
    refine ⟨a, ha, hae, hp, hm, Or.inl ⟨?_, hpos⟩⟩
    rw [chart.loopDeg_complexMapLoop_sub_const γ hclosed (a : ℂ) hp,
      chart.loopDeg_complexMapLoop_sub_const γ hclosed (-(a : ℂ)) hm]
    exact hd
  · obtain ⟨a, ha, hae, hp, hm, hd⟩ :=
      exists_winding_jump_of_reverse_local_crossing γ hclosed hε hu huv hvw hw hzero hneg hpos
    refine ⟨a, ha, hae, hp, hm, Or.inr ⟨?_, hneg⟩⟩
    rw [chart.loopDeg_complexMapLoop_sub_const γ hclosed (a : ℂ) hp,
      chart.loopDeg_complexMapLoop_sub_const γ hclosed (-(a : ℂ)) hm]
    exact hd

/-- Multiplying a loop and its base point by a fixed nonzero complex number
preserves the winding degree. -/
theorem loopDeg_mul_const_sub_const (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    (c q : ℂ) (hc : c ≠ 0) (hq : ∀ t, γ t ≠ q) :
    loopDeg (ContinuousMap.const unitInterval c * γ -
        ContinuousMap.const unitInterval (c * q))
      (fun t => by
        change c * γ t - c * q ≠ 0
        rw [← mul_sub]
        exact mul_ne_zero hc (sub_ne_zero.mpr (hq t))) =
      loopDeg (γ - ContinuousMap.const unitInterval q) (fun t => sub_ne_zero.mpr (hq t)) := by
  let η := γ - ContinuousMap.const unitInterval q
  have hη : ∀ t, η t ≠ 0 := fun t => sub_ne_zero.mpr (hq t)
  have hηclosed : η 0 = η 1 := by change γ 0 - q = γ 1 - q; rw [hclosed]
  have he := loopDeg_mul (ContinuousMap.const unitInterval c) η (fun _ => hc) hη rfl hηclosed
  have hmap : ContinuousMap.const unitInterval c * η =
      ContinuousMap.const unitInterval c * γ - ContinuousMap.const unitInterval (c * q) := by
    ext t
    change c * (γ t - q) = c * γ t - c * q
    exact mul_sub c (γ t) q
  simpa only [hmap, loopDeg_const c hc, zero_add] using he

/-- A loop crossing the origin from positive to negative real coordinates
has a unit winding jump between small imaginary offsets. -/
theorem exists_winding_jump_of_horizontal_crossing
    (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    {ε : ℝ} (hε : 0 < ε)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hw : w < 1)
    (hzero : ∀ t : unitInterval, γ t = 0 ↔ (t : ℝ) = v)
    (hpos : ∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → 0 < (γ t).re)
    (hneg : ∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → (γ t).re < 0) :
    ∃ (a : ℝ) (_ : 0 < a) (_ : a < ε)
        (hp : ∀ t, γ t ≠ (a : ℂ) / Complex.I)
        (hm : ∀ t, γ t ≠ -(a : ℂ) / Complex.I),
      loopDeg (γ - ContinuousMap.const unitInterval ((a : ℂ) / Complex.I))
          (fun t => sub_ne_zero.mpr (hp t)) -
        loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ) / Complex.I))
          (fun t => sub_ne_zero.mpr (hm t)) = 1 := by
  let δ := ContinuousMap.const unitInterval Complex.I * γ
  have hδclosed : δ 0 = δ 1 := by
    change Complex.I * γ 0 = Complex.I * γ 1
    rw [hclosed]
  have hδzero : ∀ t : unitInterval, δ t = 0 ↔ (t : ℝ) = v := by
    intro t
    change Complex.I * γ t = 0 ↔ _
    simpa only [mul_eq_zero, Complex.I_ne_zero, false_or] using hzero t
  obtain ⟨a, ha, hae, hp, hm, hd⟩ :=
    exists_winding_jump_of_local_crossing δ hδclosed hε hu huv hvw hw hδzero
      (by intro t ht₁ ht₂; simpa [δ, Complex.mul_im] using hpos t ht₁ ht₂)
      (by intro t ht₁ ht₂; simpa [δ, Complex.mul_im] using hneg t ht₁ ht₂)
  have hp' : ∀ t, γ t ≠ (a : ℂ) / Complex.I := by
    intro t h
    apply hp t
    change Complex.I * γ t = _
    rw [h]
    field_simp
  have hm' : ∀ t, γ t ≠ -(a : ℂ) / Complex.I := by
    intro t h
    apply hm t
    change Complex.I * γ t = _
    rw [h]
    field_simp
  have hpdeg := loopDeg_mul_const_sub_const γ hclosed Complex.I
    ((a : ℂ) / Complex.I) Complex.I_ne_zero hp'
  have hmdeg := loopDeg_mul_const_sub_const γ hclosed Complex.I
    (-(a : ℂ) / Complex.I) Complex.I_ne_zero hm'
  have hrotp : Complex.I * ((a : ℂ) / Complex.I) = (a : ℂ) := by field_simp
  have hrotm : Complex.I * (-(a : ℂ) / Complex.I) = -(a : ℂ) := by field_simp
  have hpdeg' : loopDeg (δ - ContinuousMap.const unitInterval (a : ℂ))
      (fun t => sub_ne_zero.mpr (hp t)) =
      loopDeg (γ - ContinuousMap.const unitInterval ((a : ℂ) / Complex.I))
        (fun t => sub_ne_zero.mpr (hp' t)) := by
    simpa only [hrotp] using hpdeg
  have hmdeg' : loopDeg (δ - ContinuousMap.const unitInterval (-(a : ℂ)))
      (fun t => sub_ne_zero.mpr (hm t)) =
      loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ) / Complex.I))
        (fun t => sub_ne_zero.mpr (hm' t)) := by
    simpa only [hrotm] using hmdeg
  refine ⟨a, ha, hae, hp', hm', ?_⟩
  omega

/-- A loop crossing the origin from negative to positive real coordinates
has a negative unit winding jump between small imaginary offsets. -/
theorem exists_winding_jump_of_reverse_horizontal_crossing
    (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    {ε : ℝ} (hε : 0 < ε)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hw : w < 1)
    (hzero : ∀ t : unitInterval, γ t = 0 ↔ (t : ℝ) = v)
    (hneg : ∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → (γ t).re < 0)
    (hpos : ∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → 0 < (γ t).re) :
    ∃ (a : ℝ) (_ : 0 < a) (_ : a < ε)
        (hp : ∀ t, γ t ≠ (a : ℂ) / Complex.I)
        (hm : ∀ t, γ t ≠ -(a : ℂ) / Complex.I),
      loopDeg (γ - ContinuousMap.const unitInterval ((a : ℂ) / Complex.I))
          (fun t => sub_ne_zero.mpr (hp t)) -
        loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ) / Complex.I))
          (fun t => sub_ne_zero.mpr (hm t)) = -1 := by
  let δ := ContinuousMap.const unitInterval Complex.I * γ
  have hδclosed : δ 0 = δ 1 := by
    change Complex.I * γ 0 = Complex.I * γ 1
    rw [hclosed]
  have hδzero : ∀ t : unitInterval, δ t = 0 ↔ (t : ℝ) = v := by
    intro t
    change Complex.I * γ t = 0 ↔ _
    simpa only [mul_eq_zero, Complex.I_ne_zero, false_or] using hzero t
  obtain ⟨a, ha, hae, hp, hm, hd⟩ :=
    exists_winding_jump_of_reverse_local_crossing δ hδclosed hε hu huv hvw hw hδzero
      (by intro t ht₁ ht₂; simpa [δ, Complex.mul_im] using hneg t ht₁ ht₂)
      (by intro t ht₁ ht₂; simpa [δ, Complex.mul_im] using hpos t ht₁ ht₂)
  have hp' : ∀ t, γ t ≠ (a : ℂ) / Complex.I := by
    intro t h
    apply hp t
    change Complex.I * γ t = _
    rw [h]
    field_simp
  have hm' : ∀ t, γ t ≠ -(a : ℂ) / Complex.I := by
    intro t h
    apply hm t
    change Complex.I * γ t = _
    rw [h]
    field_simp
  have hpdeg := loopDeg_mul_const_sub_const γ hclosed Complex.I
    ((a : ℂ) / Complex.I) Complex.I_ne_zero hp'
  have hmdeg := loopDeg_mul_const_sub_const γ hclosed Complex.I
    (-(a : ℂ) / Complex.I) Complex.I_ne_zero hm'
  have hrotp : Complex.I * ((a : ℂ) / Complex.I) = (a : ℂ) := by field_simp
  have hrotm : Complex.I * (-(a : ℂ) / Complex.I) = -(a : ℂ) := by field_simp
  have hpdeg' : loopDeg (δ - ContinuousMap.const unitInterval (a : ℂ))
      (fun t => sub_ne_zero.mpr (hp t)) =
      loopDeg (γ - ContinuousMap.const unitInterval ((a : ℂ) / Complex.I))
        (fun t => sub_ne_zero.mpr (hp' t)) := by
    simpa only [hrotp] using hpdeg
  have hmdeg' : loopDeg (δ - ContinuousMap.const unitInterval (-(a : ℂ)))
      (fun t => sub_ne_zero.mpr (hm t)) =
      loopDeg (γ - ContinuousMap.const unitInterval (-(a : ℂ) / Complex.I))
        (fun t => sub_ne_zero.mpr (hm' t)) := by
    simpa only [hrotm] using hmdeg
  refine ⟨a, ha, hae, hp', hm', ?_⟩
  omega

/-- A horizontal crossing in chart coordinates gives the corresponding signed
winding jump for the image loop about the images of the two vertical offsets. -/
theorem Source.OrientedChart.exists_winding_jump_complexMapLoop_horizontal
    (chart : Source.OrientedChart) (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    {ε : ℝ} (hε : 0 < ε)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) (hw : w < 1)
    (hzero : ∀ t : unitInterval, γ t = 0 ↔ (t : ℝ) = v)
    (hcross : (∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → 0 < (γ t).re) ∧
        (∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → (γ t).re < 0) ∨
      (∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → (γ t).re < 0) ∧
        (∀ t : unitInterval, v < (t : ℝ) → (t : ℝ) ≤ w → 0 < (γ t).re)) :
    ∃ (a : ℝ) (_ : 0 < a) (_ : a < ε)
        (hp : ∀ t, γ t ≠ (a : ℂ) / Complex.I)
        (hm : ∀ t, γ t ≠ -(a : ℂ) / Complex.I),
      let d := loopDeg (chart.complexMapLoop γ -
          ContinuousMap.const unitInterval (chart.complexMap ((a : ℂ) / Complex.I)))
        (fun t => sub_ne_zero.mpr (fun h => hp t (chart.complexMap.injective h))) -
        loopDeg (chart.complexMapLoop γ -
          ContinuousMap.const unitInterval (chart.complexMap (-(a : ℂ) / Complex.I)))
        (fun t => sub_ne_zero.mpr (fun h => hm t (chart.complexMap.injective h)))
      (d = 1 ∧ (∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → 0 < (γ t).re)) ∨
        (d = -1 ∧ (∀ t : unitInterval, u ≤ (t : ℝ) → (t : ℝ) < v → (γ t).re < 0)) := by
  rcases hcross with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · obtain ⟨a, ha, hae, hp, hm, hd⟩ :=
      exists_winding_jump_of_horizontal_crossing γ hclosed hε hu huv hvw hw hzero hpos hneg
    refine ⟨a, ha, hae, hp, hm, Or.inl ⟨?_, hpos⟩⟩
    rw [chart.loopDeg_complexMapLoop_sub_const γ hclosed ((a : ℂ) / Complex.I) hp,
      chart.loopDeg_complexMapLoop_sub_const γ hclosed (-(a : ℂ) / Complex.I) hm]
    exact hd
  · obtain ⟨a, ha, hae, hp, hm, hd⟩ :=
      exists_winding_jump_of_reverse_horizontal_crossing γ hclosed hε hu huv hvw hw
        hzero hneg hpos
    refine ⟨a, ha, hae, hp, hm, Or.inr ⟨?_, hneg⟩⟩
    rw [chart.loopDeg_complexMapLoop_sub_const γ hclosed ((a : ℂ) / Complex.I) hp,
      chart.loopDeg_complexMapLoop_sub_const γ hclosed (-(a : ℂ) / Complex.I) hm]
    exact hd

/-- A recentered chart image has the same winding degree about the recentered
image of any point avoided by the original loop. -/
theorem Source.OrientedChart.loopDeg_mapLoop_sub_const
    (chart : Source.OrientedChart) (q z : ℂ) (γ : C(unitInterval, ℂ))
    (hclosed : γ 0 = γ 1) (hz : ∀ t, γ t ≠ z) :
    loopDeg (chart.mapLoop q γ - ContinuousMap.const unitInterval
        (chart.complexMap (q + z) - chart.complexMap q))
      (fun t => by
        apply sub_ne_zero.mpr
        intro he
        apply hz t
        rw [chart.mapLoop_apply] at he
        change chart.complexMap (q + γ t) - chart.complexMap q =
          chart.complexMap (q + z) - chart.complexMap q at he
        have h : chart.complexMap (q + γ t) = chart.complexMap (q + z) := by
          linear_combination he
        exact add_left_cancel (chart.complexMap.injective h)) =
      loopDeg (γ - ContinuousMap.const unitInterval z) (fun t => sub_ne_zero.mpr (hz t)) := by
  let δ := ContinuousMap.const unitInterval q + γ
  have hc : δ 0 = δ 1 := by change q + γ 0 = q + γ 1; rw [hclosed]
  have hn : ∀ t, δ t ≠ q + z := by
    intro t he
    exact hz t (add_left_cancel he)
  have h := chart.loopDeg_complexMapLoop_sub_const δ hc (q + z) hn
  have he : chart.complexMapLoop δ - ContinuousMap.const unitInterval (chart.complexMap (q + z)) =
      chart.mapLoop q γ - ContinuousMap.const unitInterval
        (chart.complexMap (q + z) - chart.complexMap q) := by
    ext t
    change chart.complexMap (q + γ t) - chart.complexMap (q + z) = _
    rw [ContinuousMap.sub_apply, ContinuousMap.const_apply, chart.mapLoop_apply]
    change chart.complexMap (q + γ t) - chart.complexMap (q + z) =
      (chart.complexMap (q + γ t) - chart.complexMap q) -
        (chart.complexMap (q + z) - chart.complexMap q)
    ring
  have he' : δ - ContinuousMap.const unitInterval (q + z) =
      γ - ContinuousMap.const unitInterval z := by
    ext t
    change q + γ t - (q + z) = γ t - z
    ring
  simpa only [he, he'] using h

/-- Two equal positive winding jumps cannot have both their sides matched in
reverse within complementary components of the same loop. -/
theorem not_crossed_component_matching_of_winding_jumps
    (γ : C(unitInterval, ℂ)) (hclosed : γ 0 = γ 1)
    {p₁ p₂ q₁ q₂ : ℂ}
    (hp₁ : p₁ ∉ Set.range γ) (hp₂ : p₂ ∉ Set.range γ)
    (hq₁ : q₁ ∉ Set.range γ) (hq₂ : q₂ ∉ Set.range γ)
    (hpdeg : loopDeg (γ - ContinuousMap.const unitInterval p₁)
        (fun t => sub_ne_zero.mpr (fun h => hp₁ ⟨t, h⟩)) -
      loopDeg (γ - ContinuousMap.const unitInterval p₂)
        (fun t => sub_ne_zero.mpr (fun h => hp₂ ⟨t, h⟩)) = 1)
    (hqdeg : loopDeg (γ - ContinuousMap.const unitInterval q₁)
        (fun t => sub_ne_zero.mpr (fun h => hq₁ ⟨t, h⟩)) -
      loopDeg (γ - ContinuousMap.const unitInterval q₂)
        (fun t => sub_ne_zero.mpr (fun h => hq₂ ⟨t, h⟩)) = 1) :
    ¬ (q₂ ∈ connectedComponentIn (Set.range γ)ᶜ p₁ ∧
      q₁ ∈ connectedComponentIn (Set.range γ)ᶜ p₂) := by
  rintro ⟨h₁, h₂⟩
  have heq₁ := loopDeg_sub_const_eq_of_connectedComponentIn γ hclosed hp₁ h₁
  have heq₂ := loopDeg_sub_const_eq_of_connectedComponentIn γ hclosed hp₂ h₂
  omega

end
end FiniteAvalanches.Electrical
