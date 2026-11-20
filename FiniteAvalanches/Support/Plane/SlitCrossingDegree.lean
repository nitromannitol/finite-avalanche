import FiniteAvalanches.Support.Plane.TopoDegree
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.LeftRight

/-!
# Degree of a loop crossing the negative real axis once

A closed nonvanishing loop that avoids the closed negative real axis has degree
zero. If it meets that axis exactly once, passing from the upper half plane to
the lower half plane, its degree is one; in the opposite direction it is minus
one. The continuous logarithm is the principal logarithm, corrected by `2πi`
after the crossing.
-/

namespace FiniteAvalanches.Electrical

open QuantumZipper.CA.Topo
open Complex Set Filter Topology
open scoped ComplexConjugate Real

/-- Degrees of loops agree when the loops agree. -/
theorem loopDeg_congr {γ γ' : C(unitInterval, ℂ)} (h : γ = γ') (hγ : ∀ t, γ t ≠ 0)
    (hγ' : ∀ t, γ' t ≠ 0) : loopDeg γ hγ = loopDeg γ' hγ' := by
  subst h
  rfl

/-- A closed loop in the slit plane has degree zero. -/
theorem loopDeg_eq_zero_of_mem_slitPlane (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0)
    (hc : δ 0 = δ 1) (hslit : ∀ t, δ t ∈ slitPlane) : loopDeg δ hδ = 0 := by
  apply loopDeg_unique δ hδ hc (L := fun t => Complex.log (δ t))
  · exact continuous_iff_continuousAt.mpr fun t =>
      (continuousAt_clog (hslit t)).comp δ.continuous.continuousAt
  · intro t
    exact Complex.exp_log (hδ t)
  · simp [hc]

/-- The pointwise conjugate of a loop. -/
noncomputable def conjLoop (δ : C(unitInterval, ℂ)) : C(unitInterval, ℂ) :=
  ⟨fun t => conj (δ t), Complex.continuous_conj.comp δ.continuous⟩

/-- Conjugation reverses the degree of a loop. -/
theorem loopDeg_conjLoop (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (hc : δ 0 = δ 1)
    (hδ' : ∀ t, conjLoop δ t ≠ 0) : loopDeg (conjLoop δ) hδ' = -loopDeg δ hδ := by
  obtain ⟨L, hL⟩ := exists_lift_exp δ hδ
  have e := loopDeg_eq_of_lift δ hδ hc L.continuous hL
  apply loopDeg_unique (conjLoop δ) hδ' (by simp [conjLoop, hc]) (L := fun t => conj (L t))
    (Complex.continuous_conj.comp L.continuous)
  · intro t
    change Complex.exp (conj (L t)) = conj (δ t)
    rw [Complex.exp_conj, hL]
  · have h := congrArg conj e
    simp only [map_sub, map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat] at h
    rw [h]
    push_cast
    ring

/-- The principal logarithm of a negative real number. -/
theorem log_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    Complex.log z = (Real.log ‖z‖ : ℂ) + π * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_eq_pi_iff.mpr ⟨hre, him⟩]

/-- A loop meeting the closed negative real axis once, from the upper half plane
to the lower half plane, has degree one. -/
theorem loopDeg_eq_one_of_slit_crossing (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0)
    (hc : δ 0 = δ 1) (t₀ : unitInterval) (ht₀ : 0 < (t₀ : ℝ)) (ht₁ : (t₀ : ℝ) < 1)
    (hslit : ∀ t, t ≠ t₀ → δ t ∈ slitPlane) (hre : (δ t₀).re < 0) (him : (δ t₀).im = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hbefore : ∀ t : unitInterval, (t₀ : ℝ) - ε < t → (t : ℝ) < t₀ → 0 < (δ t).im)
    (hafter : ∀ t : unitInterval, (t₀ : ℝ) < t → (t : ℝ) < t₀ + ε → (δ t).im < 0) :
    loopDeg δ hδ = 1 := by
  set η : ℝ := min ε (min (t₀ : ℝ) (1 - t₀)) with hη
  have hη0 : 0 < η := lt_min hε (lt_min ht₀ (by linarith))
  have hηε : η ≤ ε := min_le_left _ _
  have hηt : η ≤ t₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1 - t₀ := (min_le_right _ _).trans (min_le_right _ _)
  let f : ℝ → ℂ := fun s => δ (projIcc 0 1 zero_le_one s)
  have hf : Continuous f := δ.continuous.comp continuous_projIcc
  have hfI : ∀ t : unitInterval, f t = δ t := fun t => by
    simp only [f, projIcc_val]
  have hfslit : ∀ s : ℝ, s ≠ t₀ → f s ∈ slitPlane := by
    intro s hs
    apply hslit
    intro h
    apply hs
    have h' := congrArg Subtype.val h
    rw [coe_projIcc] at h'
    rcases le_or_gt s 0 with h0 | h0
    · rw [max_eq_left (min_le_of_right_le h0)] at h'
      linarith
    · rcases le_or_gt s 1 with h1 | h1
      · rw [min_eq_right h1, max_eq_right h0.le] at h'
        exact h'
      · rw [min_eq_left h1.le, max_eq_right zero_le_one] at h'
        linarith
  let L' : ℝ → ℂ := fun s => Complex.log (f s) + if (t₀ : ℝ) < s then 2 * π * I else 0
  have hlogf : ∀ s, s ≠ (t₀ : ℝ) → ContinuousAt (fun s => Complex.log (f s)) s := fun s hs =>
    (continuousAt_clog (hfslit s hs)).comp hf.continuousAt
  have hcont : Continuous L' := by
    refine continuous_iff_continuousAt.mpr fun s => ?_
    rcases lt_trichotomy s t₀ with hs | hs | hs
    · have heq : (fun s => Complex.log (f s)) =ᶠ[𝓝 s] L' := by
        filter_upwards [Iio_mem_nhds hs] with u hu
        simp only [L', if_neg (not_lt.mpr (le_of_lt (mem_Iio.mp hu))), add_zero]
      exact (hlogf s hs.ne).congr heq
    · subst hs
      rw [continuousAt_iff_continuous_left_right]
      constructor
      · have hmaps : MapsTo f (Iic (t₀ : ℝ) ∩ Ioi ((t₀ : ℝ) - η)) {z : ℂ | 0 ≤ z.im} := by
          rintro u ⟨hu1, hu2⟩
          rcases eq_or_lt_of_le (mem_Iic.mp hu1) with hu | hu
          · rw [hu, hfI]
            exact him.ge
          · have hu0 : 0 ≤ u := by simp only [mem_Ioi] at hu2; linarith
            have hu1' : u ≤ 1 := by linarith
            have h := hbefore ⟨u, hu0, hu1'⟩ (by simp only [mem_Ioi] at hu2; change _ < u; linarith)
              (by exact hu)
            rw [show f u = δ ⟨u, hu0, hu1'⟩ from hfI ⟨u, hu0, hu1'⟩]
            exact h.le
        have hlog := (continuousWithinAt_log_of_re_neg_of_im_zero
          (by rw [hfI]; exact hre) (by rw [hfI]; exact him)).comp
            hf.continuousAt.continuousWithinAt hmaps
        have hlog' := (continuousWithinAt_inter
          (Ioi_mem_nhds (by linarith : (t₀ : ℝ) - η < t₀))).mp hlog
        apply hlog'.congr
        · intro u hu
          simp only [L', if_neg (not_lt.mpr (mem_Iic.mp hu)), add_zero, Function.comp_apply]
        · simp only [L', lt_irrefl, if_false, add_zero, Function.comp_apply]
      · rw [← continuousWithinAt_Ioi_iff_Ici]
        have hmaps : ∀ᶠ u in 𝓝[>] (t₀ : ℝ), f u ∈ {z : ℂ | z.im < 0} := by
          filter_upwards [Ioo_mem_nhdsGT (by linarith : (t₀ : ℝ) < t₀ + η)] with u hu
          have hu0 : 0 ≤ u := by linarith [hu.1]
          have hu1 : u ≤ 1 := by linarith [hu.2]
          rw [show f u = δ ⟨u, hu0, hu1⟩ from hfI ⟨u, hu0, hu1⟩]
          exact hafter ⟨u, hu0, hu1⟩ hu.1 (by change u < _; linarith [hu.2])
        have hfT : Tendsto f (𝓝[>] (t₀ : ℝ)) (𝓝[{z : ℂ | z.im < 0}] (f t₀)) :=
          tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, hmaps⟩
        have hlogT := (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
          (by rw [hfI]; exact hre) (by rw [hfI]; exact him)).comp hfT
        have hsum := hlogT.add (tendsto_const_nhds (x := 2 * π * I))
        have hval : (Real.log ‖f t₀‖ : ℂ) - π * I + 2 * π * I = L' t₀ := by
          simp only [L', lt_irrefl, if_false, add_zero]
          rw [log_of_re_neg_of_im_zero (by rw [hfI]; exact hre) (by rw [hfI]; exact him)]
          ring
        rw [hval] at hsum
        apply hsum.congr'
        filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [L', Function.comp_apply, if_pos (show (t₀ : ℝ) < u from hu)]
    · have heq : (fun s => Complex.log (f s) + 2 * π * I) =ᶠ[𝓝 s] L' := by
        filter_upwards [Ioi_mem_nhds hs] with u hu
        simp only [L', if_pos (show (t₀ : ℝ) < u from hu)]
      exact ((hlogf s hs.ne').add continuousAt_const).congr heq
  apply loopDeg_unique δ hδ hc (L := fun t => L' t) (hcont.comp continuous_subtype_val)
  · intro t
    simp only [L', hfI]
    split_ifs
    · rw [Complex.exp_add, Complex.exp_log (hδ t), Complex.exp_two_pi_mul_I, mul_one]
    · rw [add_zero, Complex.exp_log (hδ t)]
  · have hf1 : f 1 = δ 1 := by simpa only [Set.Icc.coe_one] using hfI 1
    have hf0 : f 0 = δ 0 := by simpa only [Set.Icc.coe_zero] using hfI 0
    simp only [L', Set.Icc.coe_one, Set.Icc.coe_zero, if_pos ht₁,
      if_neg (not_lt.mpr ht₀.le)]
    rw [hf1, hf0, hc]
    push_cast
    ring

/-- A loop meeting the closed negative real axis once, from the lower half plane
to the upper half plane, has degree minus one. -/
theorem loopDeg_eq_neg_one_of_slit_crossing (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0)
    (hc : δ 0 = δ 1) (t₀ : unitInterval) (ht₀ : 0 < (t₀ : ℝ)) (ht₁ : (t₀ : ℝ) < 1)
    (hslit : ∀ t, t ≠ t₀ → δ t ∈ slitPlane) (hre : (δ t₀).re < 0) (him : (δ t₀).im = 0)
    {ε : ℝ} (hε : 0 < ε)
    (hbefore : ∀ t : unitInterval, (t₀ : ℝ) - ε < t → (t : ℝ) < t₀ → (δ t).im < 0)
    (hafter : ∀ t : unitInterval, (t₀ : ℝ) < t → (t : ℝ) < t₀ + ε → 0 < (δ t).im) :
    loopDeg δ hδ = -1 := by
  have hδ' : ∀ t, conjLoop δ t ≠ 0 := fun t => by
    simpa only [conjLoop, ContinuousMap.coe_mk, map_ne_zero] using hδ t
  have h1 : loopDeg (conjLoop δ) hδ' = 1 := by
    apply loopDeg_eq_one_of_slit_crossing (conjLoop δ) hδ' (by simp [conjLoop, hc]) t₀ ht₀ ht₁
      _ (by simpa [conjLoop] using hre) (by simp [conjLoop, him]) hε
    · intro t h h'
      simpa [conjLoop] using hbefore t h h'
    · intro t h h'
      simpa [conjLoop] using hafter t h h'
    · intro t ht
      have h := hslit t ht
      rw [mem_slitPlane_iff] at h ⊢
      simpa [conjLoop] using h
  rw [loopDeg_conjLoop δ hδ hc hδ'] at h1
  linarith

end FiniteAvalanches.Electrical
