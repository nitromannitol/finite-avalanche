import FiniteAvalanches.Sandpile.TranslationEquivariance
import FiniteAvalanches.Probability.Radius.RealThresholds
import FiniteAvalanches.Probability.Radius.Tails
import FiniteAvalanches.Probability.TailNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import FiniteAvalanches.Sandpile.ExtendedObservables
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace FiniteAvalanches.Probability.MainTailTransfer
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- The deterministic inclusion uses the original total count, including infinity. -/
theorem total_tail_subset_radius_tail (o : Site2) (R t : ℝ) (hR : 0 ≤ R)
    (ht : (8 * (⌊R⌋₊ + 1)^4 : ℕ) ≤ t) :
    {η : StableField | ENNReal.ofReal t < extendedCount (totalTopplings η o)} ⊆
      {η | ENNReal.ofReal R < extendedCount (radius η o)} := by
  rw [real_radius_tail_eq_floor o R hR]
  intro η hη
  change ENNReal.ofReal t < extendedCount (totalTopplings η o) at hη
  by_contra hn
  have hq := totalTopplings_le_of_radius_le η o ⌊R⌋₊ (le_of_not_gt hn)
  cases he : totalTopplings η o using WithTop.recTopCoe with
  | top =>
    rw [he] at hq
    exact (WithTop.not_top_le_coe _) hq
  | coe n =>
    rw [he] at hq hη
    have hn := WithTop.coe_le_coe.mp hq
    have hnn : (n : ℝ) ≤ t := (by exact_mod_cast hn : (n : ℝ) ≤
      (8 * (⌊R⌋₊ + 1)^4 : ℕ)).trans ht
    exact (not_lt_of_ge (show (n : ℝ≥0∞) ≤ ENNReal.ofReal t from
      by simpa using ENNReal.ofReal_le_ofReal hnn)) hη

/-- A nonstabilizing field stays in both real tail events at every finite threshold. -/
theorem nonstabilizing_in_both_tails (η : StableField) (o : Site2)
    (hn : ¬ FiniteStabilizable η o) (R : ℝ) :
    ENNReal.ofReal R < extendedCount (radius η o) ∧
      ENNReal.ofReal R < extendedCount (totalTopplings η o) := by
  rw [(radius_eq_top_iff η o).mpr hn, (totalTopplings_eq_top_iff η o).mpr hn]
  exact ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

/-- Translation moves the source and preserves the whole real-threshold event. -/
theorem radius_tail_measure_eq_origin (μ : Measure StableField)
    (hμ : ∀ z : Site2, MeasurePreserving (translate z) μ μ) (o : Site2) (R : ℝ) :
    μ {η | ENNReal.ofReal R < extendedCount (radius η o)} =
      μ {η | ENNReal.ofReal R < extendedCount (radius η 0)} := by
  have he : (translate o) ⁻¹' {η | ENNReal.ofReal R < extendedCount (radius η 0)} =
      {η | ENNReal.ofReal R < extendedCount (radius η o)} := by
    ext η
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have h := radius_translate η o o
    simpa using congrArg (fun n => ENNReal.ofReal R < extendedCount n) h
  rw [← he]
  exact (hμ o).measure_preimage (measurableSet_radius_tail 0 R).nullMeasurableSet

private theorem polynomial_bound (x : ℝ) (hx : 0 ≤ x) :
    8 * (x + 1)^4 + 2 ≤ (x + 2)^8 := by
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- The exponent-eight rescaling is uniform in the source and retains all extended values. -/
theorem total_tail_subset_rescaled_radius_tail (o : Site2) (t : ℝ)
    (ht : 254 ≤ t) :
    {η : StableField | ENNReal.ofReal t < extendedCount (totalTopplings η o)} ⊆
      {η | ENNReal.ofReal (Real.exp (Real.log (t + 2) / 8) - 2) <
        extendedCount (radius η o)} := by
  have ht2 : 0 < t + 2 := by linarith
  let r := Real.exp (Real.log (t + 2) / 8) - 2
  have hr : 0 ≤ r := by
    have hh : 8 * Real.log 2 ≤ Real.log (t + 2) := by
      have h := Real.log_le_log (show (0 : ℝ) < 2^8 by norm_num)
        (show (2 : ℝ)^8 ≤ t + 2 by norm_num; linarith)
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hh' : Real.log 2 ≤ Real.log (t + 2) / 8 := by linarith
    have he := Real.exp_le_exp.mpr hh'
    rw [Real.exp_log (show (0 : ℝ) < 2 by norm_num)] at he
    dsimp [r]
    linarith
  apply total_tail_subset_radius_tail o r t hr
  have hfloor : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr
  have hb := polynomial_bound (⌊r⌋₊ : ℝ) (Nat.cast_nonneg _)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (⌊r⌋₊ : ℝ) + 2)
    (show (⌊r⌋₊ : ℝ) + 2 ≤ r + 2 by linarith) 8
  have he : (r + 2)^8 = t + 2 := by
    dsimp [r]
    rw [sub_add_cancel, ← Real.exp_nat_mul]
    have hmul : (8 : ℝ) * (Real.log (t + 2) / 8) = Real.log (t + 2) := by ring
    norm_num only [Nat.cast_ofNat]
    rw [hmul, Real.exp_log ht2]
  rw [he] at hp
  have hb' : (8 * (⌊r⌋₊ + 1)^4 : ℕ) + (2 : ℝ) ≤ t + 2 := by
    exact_mod_cast hb.trans hp
  linarith

/-- An origin radius estimate gives one universal constant for both literal tails. -/
theorem internal_joint_tail_of_origin_radius_tail (μ : Measure StableField)
    [IsProbabilityMeasure μ]
    (hμ : ∀ z : Site2, MeasurePreserving (translate z) μ μ)
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hB : ∀ R : ℝ, 0 ≤ R → μ {η | ENNReal.ofReal R < extendedCount (radius η 0)} ≤
      ENNReal.ofReal (C * Real.log (R + 2) ^ (-a))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (o : Site2) (R : ℝ), 0 ≤ R →
      μ {η | ENNReal.ofReal R < extendedCount (radius η o)} +
        μ {η | ENNReal.ofReal R < extendedCount (totalTopplings η o)} ≤
      ENNReal.ofReal (D * Real.log (R + 2) ^ (-a)) := by
  let D := C + C * (8 : ℝ)^a + 2 * Real.log 256 ^ a
  have hDn : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hDn, ?_⟩
  intro o R hR
  have hlog : 0 < Real.log (R + 2) := Real.log_pos (by linarith)
  have hrad : μ {η | ENNReal.ofReal R < extendedCount (radius η o)} ≤
      ENNReal.ofReal (C * Real.log (R + 2) ^ (-a)) := by
    rw [radius_tail_measure_eq_origin μ hμ]
    exact hB R hR
  by_cases ht : 254 ≤ R
  · let r := Real.exp (Real.log (R + 2) / 8) - 2
    have hr : 0 ≤ r := by
      have hh : 8 * Real.log 2 ≤ Real.log (R + 2) := by
        have h := Real.log_le_log (show (0 : ℝ) < 2^8 by norm_num)
          (show (2 : ℝ)^8 ≤ R + 2 by norm_num; linarith)
        simpa only [Real.log_pow, Nat.cast_ofNat] using h
      have he := Real.exp_le_exp.mpr (show Real.log 2 ≤ Real.log (R + 2) / 8 by linarith)
      rw [Real.exp_log (show (0 : ℝ) < 2 by norm_num)] at he
      dsimp [r]; linarith
    have hq := (measure_mono (total_tail_subset_rescaled_radius_tail o R ht)).trans
      (show μ {η | ENNReal.ofReal r < extendedCount (radius η o)} ≤
        ENNReal.ofReal (C * Real.log (r + 2) ^ (-a)) by
        rw [radius_tail_measure_eq_origin μ hμ]; exact hB r hr)
    have he : C * Real.log (r + 2) ^ (-a) =
        C * (8 : ℝ)^a * Real.log (R + 2) ^ (-a) := by
      have hl : Real.log (r + 2) = Real.log (R + 2) / 8 := by
        dsimp [r]; rw [sub_add_cancel, Real.log_exp]
      rw [hl, Real.div_rpow hlog.le (by norm_num),
        Real.rpow_neg (show (0 : ℝ) ≤ 8 by norm_num) a]
      simp only [div_inv_eq_mul]
      ring
    rw [he] at hq
    calc
      _ ≤ ENNReal.ofReal (C * Real.log (R + 2) ^ (-a)) +
          ENNReal.ofReal (C * (8 : ℝ)^a * Real.log (R + 2) ^ (-a)) := add_le_add hrad hq
      _ = ENNReal.ofReal ((C + C * (8 : ℝ)^a) * Real.log (R + 2) ^ (-a)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (by
          dsimp [D]
          have hn : 0 ≤ 2 * Real.log 256 ^ a := by positivity
          linarith : C + C * (8 : ℝ)^a ≤ D) (by positivity))
  · have hsmall : Real.log (R + 2) ^ a ≤ Real.log 256 ^ a :=
      Real.rpow_le_rpow hlog.le (Real.log_le_log (by linarith) (by linarith)) ha.le
    have he : (2 * Real.log 256 ^ a) * Real.log (R + 2) ^ (-a) ≥ 2 := by
      rw [Real.rpow_neg hlog.le]
      have hx : 0 < Real.log (R + 2) ^ a := Real.rpow_pos_of_pos hlog a
      apply (le_mul_inv_iff₀ hx).mpr
      nlinarith
    have hb : (2 : ℝ) ≤ D * Real.log (R + 2) ^ (-a) := he.trans
      (mul_le_mul_of_nonneg_right (by
        dsimp [D]
        have hn : 0 ≤ C * (8 : ℝ)^a := by positivity
        linarith : 2 * Real.log 256 ^ a ≤ D)
        (by positivity))
    calc
      _ ≤ (1 : ℝ≥0∞) + 1 := add_le_add prob_le_one prob_le_one
      _ = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb

/-- Natural radius estimates extend to all real thresholds with a uniform factor. -/
theorem internal_real_radius_tail_of_nat_tail (μ : Measure StableField) (a C : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C)
    (hB : ∀ M : ℕ, μ {η | (M : WithTop ℕ) < radius η 0} ≤
      ENNReal.ofReal (C * Real.log (M + 2) ^ (-a))) :
    ∀ R : ℝ, 0 ≤ R → μ {η | ENNReal.ofReal R < extendedCount (radius η 0)} ≤
      ENNReal.ofReal ((C * (2 : ℝ)^a) * Real.log (R + 2) ^ (-a)) := by
  intro R hR
  rw [real_radius_tail_eq_floor 0 R hR]
  apply (hB ⌊R⌋₊).trans
  apply ENNReal.ofReal_le_ofReal
  have hn : 0 ≤ (⌊R⌋₊ : ℝ) := Nat.cast_nonneg _
  have hln : 0 < Real.log ((⌊R⌋₊ : ℝ) + 2) := Real.log_pos (by linarith)
  have hlR : 0 < Real.log (R + 2) := Real.log_pos (by linarith)
  have hfloor : R < (⌊R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one R
  have hc : R + 2 ≤ ((⌊R⌋₊ : ℝ) + 2)^2 := by nlinarith
  have hl := Real.log_le_log (show 0 < R + 2 by linarith) hc
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hm := Real.rpow_le_rpow_of_nonpos (show 0 < Real.log (R + 2) / 2 by positivity)
    (show Real.log (R + 2) / 2 ≤ Real.log ((⌊R⌋₊ : ℝ) + 2) by linarith)
    (neg_nonpos.mpr ha.le)
  have he : (Real.log (R + 2) / 2)^(-a) = (2 : ℝ)^a * Real.log (R + 2)^(-a) := by
    rw [Real.div_rpow hlR.le (by norm_num), Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) a]
    simp only [div_inv_eq_mul, mul_comm]
  rw [he] at hm
  calc
    C * Real.log ((⌊R⌋₊ : ℝ) + 2)^(-a) ≤ C * ((2 : ℝ)^a * Real.log (R + 2)^(-a)) :=
      mul_le_mul_of_nonneg_left hm hC
    _ = _ := by ring

end
end FiniteAvalanches.Probability.MainTailTransfer

namespace FiniteAvalanches.Probability.MainTailTransfer
open FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- The logarithmic majorant vanishes without changing its positive exponent. -/
theorem internal_log_tail_tendsto_zero (a C : ℝ) (ha : 0 < a) :
    Tendsto (fun R : ℝ => ENNReal.ofReal (C * Real.log (R + 2)^(-a))) atTop (nhds 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop 2 tendsto_id)
  have hh : Tendsto (fun R : ℝ => C * Real.log (R + 2)^(-a)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul ((tendsto_rpow_neg_atTop ha).comp hlog)
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hh

/-- A vanishing logarithmic tail excludes the actual infinite count. -/
theorem internal_ae_count_ne_top_of_log_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → WithTop ℕ) (a C : ℝ) (ha : 0 < a)
    (hB : ∀ R : ℝ, 0 ≤ R → μ {ω | ENNReal.ofReal R < extendedCount (X ω)} ≤
      ENNReal.ofReal (C * Real.log (R + 2) ^ (-a))) :
    ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
  rw [ae_iff]
  apply le_antisymm _ bot_le
  have hlim := internal_log_tail_tendsto_zero a C ha
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  apply (measure_mono _).trans (hB R hR)
  intro ω hω
  simp only [Set.mem_setOf_eq, not_not] at hω
  change ENNReal.ofReal R < extendedCount (X ω)
  rw [hω, extendedCount_top]
  exact ENNReal.ofReal_lt_top

/-- Layer cake and the library power-integrability criterion give every subcritical moment. -/
theorem internal_logMoment_lt_top_of_log_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → WithTop ℕ) (hX : Measurable X)
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hB : ∀ R : ℝ, 0 ≤ R → μ {ω | ENNReal.ofReal R < extendedCount (X ω)} ≤
      ENNReal.ofReal (C * Real.log (R + 2) ^ (-a)))
    (p : {p : ℝ // 0 < p}) (hp : p.val < a) :
    (∫⁻ ω, logMomentIntegrand p (X ω) ∂μ) < ⊤ := by
  let f : Ω → ℝ := fun ω => Real.log (2 + (extendedCount (X ω)).toReal)
  have hf : Measurable f :=
    (measurable_const.add ((measurable_extendedCount.comp hX).ennreal_toReal)).log
  have hfn : ∀ ω, 0 ≤ f ω := fun ω => Real.log_nonneg (by
    have := ENNReal.toReal_nonneg (a := extendedCount (X ω)); linarith)
  have he : (fun ω => logMomentIntegrand p (X ω)) =ᵐ[μ]
      (fun ω => ENNReal.ofReal (f ω ^ p.val)) := by
    filter_upwards [internal_ae_count_ne_top_of_log_tail μ X a C ha hB] with ω hω
    cases hn : X ω using WithTop.recTopCoe with
    | top => exact (hω hn).elim
    | coe n => simp [f, hn, logMomentIntegrand, extendedCount]
  rw [lintegral_congr_ae he,
    lintegral_rpow_eq_lintegral_meas_lt_mul μ (Eventually.of_forall hfn) hf.aemeasurable p.property]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  let g : ℝ → ℝ≥0∞ := fun t => μ {ω | t < f ω} * ENNReal.ofReal (t ^ (p.val - 1))
  have head : (∫⁻ t in Set.Ioc (0 : ℝ) 2, g t) < ⊤ := by
    have hi : IntegrableOn (fun t : ℝ => t ^ (p.val - 1)) (Set.Ioc 0 2) := by
      exact (intervalIntegral.intervalIntegrable_rpow' (by linarith [p.property])
        (a := 0) (b := 2)).1
    apply lt_of_le_of_lt (lintegral_mono (fun t => ?_))
      ((hasFiniteIntegral_iff_ofReal (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
        exact Real.rpow_nonneg ht.1.le _)).mp hi.hasFiniteIntegral)
    dsimp [g]
    simpa only [one_mul] using mul_le_mul_left (prob_le_one (μ := μ) (s := {ω | t < f ω}))
      (ENNReal.ofReal (t ^ (p.val - 1)))
  have tail : (∫⁻ t in Set.Ioi (2 : ℝ), g t) < ⊤ := by
    have hi := (integrableOn_Ioi_rpow_of_lt (show p.val - 1 - a < -1 by linarith)
      (show (0 : ℝ) < 2 by norm_num)).const_mul C
    apply lt_of_le_of_lt (lintegral_mono_ae ?_)
      ((hasFiniteIntegral_iff_ofReal (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_nonneg hC (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) _))).mp hi.hasFiniteIntegral)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := by linarith [Set.mem_Ioi.mp ht]
    have hR : 0 ≤ Real.exp t - 2 := by
      have hx := Real.add_one_le_exp t
      linarith [Set.mem_Ioi.mp ht]
    have hs : {ω | t < f ω} ⊆
        {ω | ENNReal.ofReal (Real.exp t - 2) < extendedCount (X ω)} := by
      intro ω hω
      change ENNReal.ofReal (Real.exp t - 2) < extendedCount (X ω)
      cases hn : X ω using WithTop.recTopCoe with
      | top => rw [extendedCount_top]; exact ENNReal.ofReal_lt_top
      | coe n =>
        have hh : Real.exp t < 2 + (n : ℝ) := by
          apply (Real.lt_log_iff_exp_lt (by positivity)).mp
          simpa [f, hn, extendedCount] using hω
        apply (ofReal_lt_extendedCount_coe _ hR n).mpr
        linarith
    have hb := (measure_mono hs).trans (hB (Real.exp t - 2) hR)
    have hl : Real.log (Real.exp t - 2 + 2) = t := by
      rw [sub_add_cancel, Real.log_exp]
    rw [hl] at hb
    dsimp [g]
    calc
      μ {ω | t < f ω} * ENNReal.ofReal (t ^ (p.val - 1)) ≤
          ENNReal.ofReal (C * t ^ (-a)) * ENNReal.ofReal (t ^ (p.val - 1)) :=
        mul_le_mul_left hb _
      _ = ENNReal.ofReal (C * t ^ (p.val - 1 - a)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg ht0.le _))]
        rw [mul_assoc, ← Real.rpow_add ht0]
        have hexp : -a + (p.val - 1) = p.val - 1 - a := by ring
        rw [hexp]
  have hu : Set.Ioi (0 : ℝ) = Set.Ioc 0 2 ∪ Set.Ioi 2 := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht; by_cases h : t ≤ 2
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht, _⟩ | ht) <;> linarith
  change (∫⁻ t in Set.Ioi (0 : ℝ), g t) < ⊤
  rw [hu]
  exact lt_of_le_of_lt (lintegral_union_le g _ _) (ENNReal.add_lt_top.mpr ⟨head, tail⟩)

end
end FiniteAvalanches.Probability.MainTailTransfer

namespace FiniteAvalanches.Probability.MainTailTransfer
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- Assembly from the still-undischarged source radius estimate. -/
theorem internal_main_conclusions_of_origin_nat_radius_tail (μ : Measure StableField)
    [IsProbabilityMeasure μ]
    (hμ : ∀ z : Site2, MeasurePreserving (translate z) μ μ)
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hB : ∀ M : ℕ, μ {η | (M : WithTop ℕ) < radius η 0} ≤
      ENNReal.ofReal (C * Real.log (M + 2) ^ (-a))) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ (o : Site2) (R : ℝ), 0 ≤ R →
        μ {η | ENNReal.ofReal R < extendedCount (radius η o)} +
          μ {η | ENNReal.ofReal R < extendedCount (totalTopplings η o)} ≤
        ENNReal.ofReal (D * Real.log (R + 2) ^ (-a))) ∧
      (∀ᵐ η ∂μ, ∀ o : Site2, FiniteStabilizable η o) ∧
      (∀ (o : Site2) (p : {p : ℝ // 0 < p}), p.val < a →
        (∫⁻ η, logMomentIntegrand p (radius η o) ∂μ) +
          (∫⁻ η, logMomentIntegrand p (totalTopplings η o) ∂μ) < ⊤) := by
  have hreal := internal_real_radius_tail_of_nat_tail μ a C ha hC hB
  obtain ⟨D, hD, htail⟩ := internal_joint_tail_of_origin_radius_tail μ hμ a
    (C * (2 : ℝ)^a) ha (by positivity) hreal
  have hr : ∀ (o : Site2) (R : ℝ), 0 ≤ R →
      μ {η | ENNReal.ofReal R < extendedCount (radius η o)} ≤
        ENNReal.ofReal (D * Real.log (R + 2)^(-a)) := by
    intro o R hR
    exact (le_self_add).trans (htail o R hR)
  have hq : ∀ (o : Site2) (R : ℝ), 0 ≤ R →
      μ {η | ENNReal.ofReal R < extendedCount (totalTopplings η o)} ≤
        ENNReal.ofReal (D * Real.log (R + 2)^(-a)) := by
    intro o R hR
    exact (le_add_self).trans (htail o R hR)
  refine ⟨D, hD, htail, ?_, ?_⟩
  · apply ae_all_finiteStabilizable_of_radius_tail_bounds μ
      (fun _ M => ENNReal.ofReal (D * Real.log ((M : ℝ) + 2)^(-a)))
    · intro o
      exact (internal_log_tail_tendsto_zero a D ha).comp tendsto_natCast_atTop_atTop
    · intro o M
      have hb := hr o (M : ℝ) (Nat.cast_nonneg _)
      simpa only [real_radius_tail_eq_floor o (M : ℝ) (Nat.cast_nonneg _),
        Nat.floor_natCast] using hb
  · intro o p hp
    exact ENNReal.add_lt_top.mpr
      ⟨internal_logMoment_lt_top_of_log_tail μ (fun η => radius η o) (measurable_radius o)
        a D ha hD (hr o) p hp,
       internal_logMoment_lt_top_of_log_tail μ (fun η => totalTopplings η o)
        (measurable_totalTopplings o) a D ha hD (hq o) p hp⟩

/-- One shared exponent and constant bind all sources, thresholds, and moment orders. -/
theorem internal_shared_main_target_of_origin_nat_radius_tail (μ : Measure StableField)
    [IsProbabilityMeasure μ]
    (hμ : ∀ z : Site2, MeasurePreserving (translate z) μ μ)
    (hB : ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      μ {η | (M : WithTop ℕ) < radius η 0} ≤
        ENNReal.ofReal (C * Real.log (M + 2)^(-a))) :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧
      (∀ (o : Site2) (R : ℝ), 0 ≤ R →
        (μ {η | ENNReal.ofReal R < extendedCount (radius η o)}).toReal +
          (μ {η | ENNReal.ofReal R < extendedCount (totalTopplings η o)}).toReal ≤
        C * Real.log (R + 2)^(-a)) ∧
      (∀ᵐ η ∂μ, ∀ o : Site2, ∃ w : List Site2, Stabilizes η (oneGrain o) w) ∧
      (∀ (o : Site2) (p : {p : ℝ // 0 < p}), p.val < a →
        (∫⁻ η, logMomentIntegrand p (radius η o) ∂μ) +
          (∫⁻ η, logMomentIntegrand p (totalTopplings η o) ∂μ) < ⊤) := by
  obtain ⟨a, ha, C, hC, hbound⟩ := hB
  obtain ⟨D, hD, ht, hs, hm⟩ :=
    internal_main_conclusions_of_origin_nat_radius_tail μ hμ a C ha hC hbound
  refine ⟨a, ha, D, hD, ?_, hs, hm⟩
  intro o R hR
  exact (real_avalanche_tail_iff μ o R D a hR hD).mpr (ht o R hR)

end
end FiniteAvalanches.Probability.MainTailTransfer
