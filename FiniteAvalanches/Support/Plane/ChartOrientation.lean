import FiniteAvalanches.Electrical.Geometry.BSST
import FiniteAvalanches.Support.Plane.TopoDegree

/-!
# Orientation of plane charts

Ported from Lattice-Probability `LatticeProb/Topology/PlaneGraph/ChartOrientation.lean` at commit `74eab009`.

The degree of a small circle around a point is preserved by a plane isotopy.
-/

namespace FiniteAvalanches.Electrical

open FiniteAvalanches.Electrical.StatementGeometry
open QuantumZipper.CA.Topo
open Complex
open scoped ComplexConjugate

noncomputable section

/-- The winding degree of a closed loop is constant as the base point moves
along a path in its complement. -/
theorem loopDeg_sub_const_eq_of_path (γ : C(unitInterval, ℂ)) (hc : γ 0 = γ 1)
    {a b : ℂ} (p : Path a b) (hp : ∀ s t, γ t ≠ p s) :
    loopDeg (γ - ContinuousMap.const unitInterval a)
        (fun t => sub_ne_zero.mpr (by
          simpa only [ContinuousMap.const_apply, Path.source] using hp 0 t)) =
      loopDeg (γ - ContinuousMap.const unitInterval b)
        (fun t => sub_ne_zero.mpr (by
          simpa only [ContinuousMap.const_apply, Path.target] using hp 1 t)) := by
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun z => γ z.1 - p z.2,
      (γ.continuous.comp continuous_fst).sub (p.continuous.comp continuous_snd)⟩
  have hH : ∀ z, H z ≠ 0 := fun z => sub_ne_zero.mpr (hp z.2 z.1)
  have hclosed : ∀ s, H (0, s) = H (1, s) := by
    intro s
    change γ 0 - p s = γ 1 - p s
    rw [hc]
  have h := loopDeg_homotopy H hH hclosed
  have h0 : slice H 0 = γ - ContinuousMap.const unitInterval a := by
    ext t
    simp only [slice, H, ContinuousMap.coe_mk, ContinuousMap.sub_apply,
      ContinuousMap.const_apply, Path.source]
  have h1 : slice H 1 = γ - ContinuousMap.const unitInterval b := by
    ext t
    simp only [slice, H, ContinuousMap.coe_mk, ContinuousMap.sub_apply,
      ContinuousMap.const_apply, Path.target]
  convert h using 1 <;> congr 1
  · exact h0.symm
  · exact h1.symm

/-- The winding degree of a closed loop is constant on each component of its
complement. -/
theorem loopDeg_sub_const_eq_of_connectedComponentIn
    (γ : C(unitInterval, ℂ)) (hc : γ 0 = γ 1) {a b : ℂ}
    (ha : a ∉ Set.range γ)
    (hb : b ∈ connectedComponentIn (Set.range γ)ᶜ a) :
    loopDeg (γ - ContinuousMap.const unitInterval a)
        (fun t => sub_ne_zero.mpr (fun h => ha ⟨t, h⟩)) =
      loopDeg (γ - ContinuousMap.const unitInterval b)
        (fun t => sub_ne_zero.mpr
          (fun h => connectedComponentIn_subset _ _ hb ⟨t, h⟩)) := by
  let U := (Set.range γ)ᶜ
  let C := connectedComponentIn U a
  have hU : IsOpen U := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hC : IsConnected C := isConnected_connectedComponentIn_iff.mpr ha
  have hpath : IsPathConnected C := (hU.connectedComponentIn).isConnected_iff_isPathConnected.mp hC
  have haC : a ∈ C := mem_connectedComponentIn ha
  obtain ⟨p, hp⟩ := hpath.joinedIn a haC b hb
  apply loopDeg_sub_const_eq_of_path γ hc p
  intro s t h
  exact connectedComponentIn_subset U a (hp s) ⟨t, h⟩

/-- A circle around a point, followed through an isotopy and recentered. -/
def Source.OrientedChart.isotopyCircle (chart : Source.OrientedChart) (q : ℂ) (r : ℝ) :
    C(unitInterval × unitInterval, ℂ) where
  toFun p := Complex.equivRealProdCLM.symm
      (chart.isotopy p.2 (Complex.equivRealProdCLM (q + circleLoop r p.1))) -
    Complex.equivRealProdCLM.symm (chart.isotopy p.2 (Complex.equivRealProdCLM q))
  continuous_toFun := by
    have h₁ : Continuous (fun p : unitInterval × unitInterval =>
        chart.isotopy p.2 (Complex.equivRealProdCLM (q + circleLoop r p.1))) :=
      chart.continuous.comp (continuous_snd.prodMk
        (Complex.equivRealProdCLM.continuous.comp (continuous_const.add
          ((circleLoop r).continuous.comp continuous_fst))))
    have h₂ : Continuous (fun p : unitInterval × unitInterval =>
        chart.isotopy p.2 (Complex.equivRealProdCLM q)) :=
      chart.continuous.comp (continuous_snd.prodMk continuous_const)
    exact (Complex.equivRealProdCLM.symm.continuous.comp h₁).sub
      (Complex.equivRealProdCLM.symm.continuous.comp h₂)

/-- The recentered image of a nondegenerate circle avoids zero. -/
theorem Source.OrientedChart.isotopyCircle_ne_zero (chart : Source.OrientedChart)
    (q : ℂ) {r : ℝ} (hr : r ≠ 0) (p : unitInterval × unitInterval) :
    chart.isotopyCircle q r p ≠ 0 := by
  intro hz
  have heq := sub_eq_zero.mp hz
  have heq' := Complex.equivRealProdCLM.symm.injective heq
  have heq'' := (chart.isotopy p.2).injective heq'
  have heq''' := Complex.equivRealProdCLM.injective heq''
  exact circleLoop_ne_zero hr p.1 (add_eq_left.mp heq''')

/-- A plane chart isotopy preserves the winding degree of a recentered circle. -/
theorem Source.OrientedChart.isotopyCircle_degree (chart : Source.OrientedChart)
    (q : ℂ) {r : ℝ} (hr : r ≠ 0) :
    loopDeg (slice (chart.isotopyCircle q r) 1)
      (fun t => chart.isotopyCircle_ne_zero q hr (t, 1)) = 1 := by
  have hclosed : ∀ s, chart.isotopyCircle q r (0, s) = chart.isotopyCircle q r (1, s) := by
    intro s
    have hloop : circleLoop r 0 = circleLoop r 1 := by
      simpa [circleLoop] using (periodic_circleMap 0 r 0).symm
    change Complex.equivRealProdCLM.symm
      (chart.isotopy s (Complex.equivRealProdCLM (q + circleLoop r 0))) - _ =
      Complex.equivRealProdCLM.symm
      (chart.isotopy s (Complex.equivRealProdCLM (q + circleLoop r 1))) - _
    rw [hloop]
  have heq := loopDeg_homotopy (chart.isotopyCircle q r)
    (chart.isotopyCircle_ne_zero q hr) hclosed
  have hstart : slice (chart.isotopyCircle q r) 0 = circleLoop r := by
    ext t
    change Complex.equivRealProdCLM.symm
      (chart.isotopy 0 (Complex.equivRealProdCLM (q + circleLoop r t))) -
      Complex.equivRealProdCLM.symm (chart.isotopy 0 (Complex.equivRealProdCLM q)) = _
    rw [show chart.isotopy 0 = Homeomorph.refl _ from chart.start]
    change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (q + circleLoop r t)) -
      Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM q) = _
    simp only [ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel_left]
  have hdeg : loopDeg (slice (chart.isotopyCircle q r) 0)
      (fun t => chart.isotopyCircle_ne_zero q hr (t, 0)) = 1 := by
    simpa only [hstart] using loopDeg_circle hr
  exact heq.symm.trans hdeg

/-- A loop followed through a chart isotopy and recentered at the image of a point. -/
def Source.OrientedChart.isotopyLoop (chart : Source.OrientedChart)
    (q : ℂ) (γ : C(unitInterval, ℂ)) : C(unitInterval × unitInterval, ℂ) where
  toFun p := Complex.equivRealProdCLM.symm
      (chart.isotopy p.2 (Complex.equivRealProdCLM (γ p.1))) -
    Complex.equivRealProdCLM.symm (chart.isotopy p.2 (Complex.equivRealProdCLM q))
  continuous_toFun := by
    have h₁ : Continuous (fun p : unitInterval × unitInterval =>
        chart.isotopy p.2 (Complex.equivRealProdCLM (γ p.1))) :=
      chart.continuous.comp (continuous_snd.prodMk
        (Complex.equivRealProdCLM.continuous.comp (γ.continuous.comp continuous_fst)))
    have h₂ : Continuous (fun p : unitInterval × unitInterval =>
        chart.isotopy p.2 (Complex.equivRealProdCLM q)) :=
      chart.continuous.comp (continuous_snd.prodMk continuous_const)
    exact (Complex.equivRealProdCLM.symm.continuous.comp h₁).sub
      (Complex.equivRealProdCLM.symm.continuous.comp h₂)

/-- Recentered chart isotopies avoid zero when the original loop avoids the center. -/
theorem Source.OrientedChart.isotopyLoop_ne_zero (chart : Source.OrientedChart)
    (q : ℂ) (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ q)
    (p : unitInterval × unitInterval) : chart.isotopyLoop q γ p ≠ 0 := by
  intro hz
  have heq := sub_eq_zero.mp hz
  have heq' := Complex.equivRealProdCLM.symm.injective heq
  have heq'' := (chart.isotopy p.2).injective heq'
  exact hγ p.1 (Complex.equivRealProdCLM.injective heq'')

/-- A chart isotopy preserves the degree of every loop around the chosen center. -/
theorem Source.OrientedChart.isotopyLoop_degree (chart : Source.OrientedChart)
    (q : ℂ) (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ q) (hc : γ 0 = γ 1) :
    loopDeg (slice (chart.isotopyLoop q γ) 1)
        (fun t => chart.isotopyLoop_ne_zero q γ hγ (t, 1)) =
      loopDeg (γ - ContinuousMap.const unitInterval q) (fun t => sub_ne_zero.mpr (hγ t)) := by
  have hclosed : ∀ s, chart.isotopyLoop q γ (0, s) = chart.isotopyLoop q γ (1, s) := by
    intro s
    change Complex.equivRealProdCLM.symm
      (chart.isotopy s (Complex.equivRealProdCLM (γ 0))) - _ =
      Complex.equivRealProdCLM.symm (chart.isotopy s (Complex.equivRealProdCLM (γ 1))) - _
    rw [hc]
  have heq := loopDeg_homotopy (chart.isotopyLoop q γ)
    (chart.isotopyLoop_ne_zero q γ hγ) hclosed
  have hstart : slice (chart.isotopyLoop q γ) 0 = γ - ContinuousMap.const unitInterval q := by
    ext t
    change Complex.equivRealProdCLM.symm
      (chart.isotopy 0 (Complex.equivRealProdCLM (γ t))) -
      Complex.equivRealProdCLM.symm (chart.isotopy 0 (Complex.equivRealProdCLM q)) = γ t - q
    rw [show chart.isotopy 0 = Homeomorph.refl _ from chart.start]
    change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) -
      Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM q) = γ t - q
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  simpa only [hstart] using heq.symm

/-- Apply a chart to a loop of offsets and recenter at the image of its center. -/
def Source.OrientedChart.mapLoop (chart : Source.OrientedChart)
    (q : ℂ) (γ : C(unitInterval, ℂ)) : C(unitInterval, ℂ) :=
  slice (chart.isotopyLoop q (ContinuousMap.const unitInterval q + γ)) 1

/-- Evaluation of a recentered chart image in complex coordinates. -/
theorem Source.OrientedChart.mapLoop_apply (chart : Source.OrientedChart)
    (q : ℂ) (γ : C(unitInterval, ℂ)) (t : unitInterval) :
    chart.mapLoop q γ t = Complex.equivRealProdCLM.symm
        (chart.map (Complex.equivRealProdCLM (q + γ t))) -
      Complex.equivRealProdCLM.symm (chart.map (Complex.equivRealProdCLM q)) := by
  change Complex.equivRealProdCLM.symm
      (chart.isotopy 1 (Complex.equivRealProdCLM (q + γ t))) -
    Complex.equivRealProdCLM.symm (chart.isotopy 1 (Complex.equivRealProdCLM q)) = _
  rw [show chart.isotopy 1 = chart.map from chart.finish]

/-- Recentered chart images of nonvanishing loops are nonvanishing. -/
theorem Source.OrientedChart.mapLoop_ne_zero (chart : Source.OrientedChart)
    (q : ℂ) (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0) :
    ∀ t, chart.mapLoop q γ t ≠ 0 := by
  intro t
  apply chart.isotopyLoop_ne_zero q (ContinuousMap.const unitInterval q + γ) ?_ (t, 1)
  intro u he
  have : γ u = 0 := by
    change q + γ u = q at he
    exact add_eq_left.mp he
  exact hγ u this

/-- Chart images preserve loop closure. -/
theorem Source.OrientedChart.mapLoop_closed (chart : Source.OrientedChart)
    (q : ℂ) (γ : C(unitInterval, ℂ)) (hc : γ 0 = γ 1) :
    chart.mapLoop q γ 0 = chart.mapLoop q γ 1 := by
  change Complex.equivRealProdCLM.symm
    (chart.isotopy 1 (Complex.equivRealProdCLM (q + γ 0))) - _ =
    Complex.equivRealProdCLM.symm
    (chart.isotopy 1 (Complex.equivRealProdCLM (q + γ 1))) - _
  rw [hc]

/-- Recentered chart images preserve the degree of a loop. -/
theorem Source.OrientedChart.mapLoop_degree (chart : Source.OrientedChart)
    (q : ℂ) (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0) (hc : γ 0 = γ 1) :
    loopDeg (chart.mapLoop q γ) (chart.mapLoop_ne_zero q γ hγ) = loopDeg γ hγ := by
  have hne : ∀ t, (ContinuousMap.const unitInterval q + γ) t ≠ q := by
    intro t he
    apply hγ t
    change q + γ t = q at he
    exact add_eq_left.mp he
  have hclosed : (ContinuousMap.const unitInterval q + γ) 0 =
      (ContinuousMap.const unitInterval q + γ) 1 := by
    change q + γ 0 = q + γ 1
    rw [hc]
  have he := chart.isotopyLoop_degree q (ContinuousMap.const unitInterval q + γ) hne hclosed
  have heq : (ContinuousMap.const unitInterval q + γ) - ContinuousMap.const unitInterval q = γ := by
    ext t
    change q + γ t - q = γ t
    exact add_sub_cancel_left _ _
  simpa only [mapLoop, heq] using he

/-- A chart maps sufficiently small circles into any prescribed neighborhood of its center. -/
theorem Source.OrientedChart.exists_small_mapLoop_circle (chart : Source.OrientedChart)
    (a : ℂ) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ t, ‖chart.mapLoop a (circleLoop r) t‖ < ε := by
  let f : ℂ → ℂ := fun z => Complex.equivRealProdCLM.symm
    (chart.map (Complex.equivRealProdCLM z))
  have hf : Continuous f := Complex.equivRealProdCLM.symm.continuous.comp
    (chart.map.continuous.comp Complex.equivRealProdCLM.continuous)
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  refine ⟨min δ R / 2, by positivity, by linarith [min_le_right δ R], ?_⟩
  intro t
  have hrδ : min δ R / 2 < δ := by linarith [min_le_left δ R]
  have hdist : dist (a + circleLoop (min δ R / 2) t) a < δ := by
    rw [dist_eq_norm, add_sub_cancel_left]
    change ‖circleMap 0 (min δ R / 2) _‖ < δ
    rw [norm_circleMap_zero, abs_of_pos (by positivity)]
    exact hrδ
  have h := hδf hdist
  rw [dist_eq_norm] at h
  change ‖Complex.equivRealProdCLM.symm
    (chart.isotopy 1 (Complex.equivRealProdCLM (a + circleLoop (min δ R / 2) t))) -
    Complex.equivRealProdCLM.symm (chart.isotopy 1 (Complex.equivRealProdCLM a))‖ < ε
  rw [show chart.isotopy 1 = chart.map from chart.finish]
  exact h

/-- Loops with corresponding points in a common open half-plane have the same degree. -/
theorem loopDeg_eq_of_coordinate_sign (γ δ : C(unitInterval, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hδ : ∀ t, δ t ≠ 0)
    (hγc : γ 0 = γ 1) (hδc : δ 0 = δ 1)
    (hsign : ∀ t, (0 < (γ t).im ∧ 0 < (δ t).im) ∨
      ((γ t).im < 0 ∧ (δ t).im < 0) ∨
      (0 < (γ t).re ∧ 0 < (δ t).re) ∨
      ((γ t).re < 0 ∧ (δ t).re < 0)) :
    loopDeg γ hγ = loopDeg δ hδ := by
  let H : C(unitInterval × unitInterval, ℂ) := ⟨fun p =>
    (1 - (p.2 : ℝ)) * γ p.1 + (p.2 : ℝ) * δ p.1, by fun_prop⟩
  have hH : ∀ p, H p ≠ 0 := by
    intro ⟨t, s⟩ hz
    have hs0 : (0 : ℝ) ≤ s := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hpos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
        0 < (1 - (s : ℝ)) * x + (s : ℝ) * y := by
      by_cases hs : (s : ℝ) = 0
      · simpa only [hs, sub_zero, one_mul, zero_mul, add_zero] using hx
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs1) hx.le)
          (mul_pos (lt_of_le_of_ne hs0 (Ne.symm hs)) hy)
    have hre : (1 - (s : ℝ)) * (γ t).re + (s : ℝ) * (δ t).re = 0 := by
      have := congrArg Complex.re hz
      simpa [H] using this
    have him : (1 - (s : ℝ)) * (γ t).im + (s : ℝ) * (δ t).im = 0 := by
      have := congrArg Complex.im hz
      simpa [H] using this
    rcases hsign t with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact (ne_of_gt (hpos _ _ ha hb)) him
    · have hp := hpos (-(γ t).im) (-(δ t).im) (neg_pos.mpr ha) (neg_pos.mpr hb)
      linarith
    · exact (ne_of_gt (hpos _ _ ha hb)) hre
    · have hp := hpos (-(γ t).re) (-(δ t).re) (neg_pos.mpr ha) (neg_pos.mpr hb)
      linarith
  have hclosed : ∀ s, H (0, s) = H (1, s) := by
    intro s
    change (1 - (s : ℝ)) * γ 0 + (s : ℝ) * δ 0 =
      (1 - (s : ℝ)) * γ 1 + (s : ℝ) * δ 1
    rw [hγc, hδc]
  have he := loopDeg_homotopy H hH hclosed
  have h0 : slice H 0 = γ := by ext t; simp [slice, H]
  have h1 : slice H 1 = δ := by ext t; simp [slice, H]
  simpa only [h0, h1] using he

/-- A loop in the closed upper half-plane that avoids zero has degree zero. -/
theorem loopDeg_eq_zero_of_im_nonneg (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hc : γ 0 = γ 1) (him : ∀ t, 0 ≤ (γ t).im) : loopDeg γ hγ = 0 := by
  let H : C(unitInterval × unitInterval, ℂ) := ⟨fun p =>
    (1 - (p.2 : ℝ)) * γ p.1 + (p.2 : ℝ) * Complex.I, by fun_prop⟩
  have hH : ∀ p, H p ≠ 0 := by
    intro ⟨t, s⟩ hz
    by_cases hs : (s : ℝ) = 0
    · apply hγ t
      have : H (t, s) = γ t := by simp [H, hs]
      exact this ▸ hz
    · have hs0 : (0 : ℝ) < s := lt_of_le_of_ne s.2.1 (Ne.symm hs)
      have hs1 : (s : ℝ) ≤ 1 := s.2.2
      have hpos : 0 < (1 - (s : ℝ)) * (γ t).im + s :=
        add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs1) (him t)) hs0
      have he := congrArg Complex.im hz
      have he' : (1 - (s : ℝ)) * (γ t).im + s = 0 := by simpa [H] using he
      exact (ne_of_gt hpos) he'
  have hclosed : ∀ s, H (0, s) = H (1, s) := by
    intro s
    change (1 - (s : ℝ)) * γ 0 + (s : ℝ) * Complex.I =
      (1 - (s : ℝ)) * γ 1 + (s : ℝ) * Complex.I
    rw [hc]
  have he := loopDeg_homotopy H hH hclosed
  have h0 : slice H 0 = γ := by ext t; simp [slice, H]
  have h1 : slice H 1 = ContinuousMap.const unitInterval Complex.I := by
    ext t; simp [slice, H]
  calc
    loopDeg γ hγ = loopDeg (ContinuousMap.const unitInterval Complex.I)
        (fun _ => Complex.I_ne_zero) := by simpa only [h0, h1] using he
    _ = 0 := loopDeg_const _ Complex.I_ne_zero

/-- Inverting a nonvanishing loop reverses its degree. -/
theorem loopDeg_inv (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hγc : γ 0 = γ 1) :
    loopDeg ⟨fun t => (γ t)⁻¹, γ.continuous.inv₀ hγ⟩
      (fun t => inv_ne_zero (hγ t)) = -loopDeg γ hγ := by
  obtain ⟨L, hL⟩ := exists_lift_exp γ hγ
  apply loopDeg_unique _ _ (by change (γ 0)⁻¹ = (γ 1)⁻¹; rw [hγc])
    (L := fun t => -L t) L.continuous.neg (fun t => by change Complex.exp (-L t) = (γ t)⁻¹; rw [Complex.exp_neg, hL])
  have he := loopDeg_eq_of_lift γ hγ hγc L.continuous hL
  push_cast
  linear_combination -he

/-- Complex conjugation reverses the degree of a loop. -/
theorem loopDeg_conj (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hc : γ 0 = γ 1) :
    loopDeg ⟨fun t => conj (γ t), continuous_conj.comp γ.continuous⟩
      (fun t => by simpa using hγ t) = -loopDeg γ hγ := by
  obtain ⟨L, hL⟩ := exists_lift_exp γ hγ
  apply loopDeg_unique _ _ (by change conj (γ 0) = conj (γ 1); rw [hc])
    (L := fun t => conj (L t)) (continuous_conj.comp L.continuous)
    (fun t => by change Complex.exp (conj (L t)) = conj (γ t); rw [exp_conj, hL])
  have he := loopDeg_eq_of_lift γ hγ hc L.continuous hL
  have he' := congrArg (fun z : ℂ => conj z) he
  simpa only [map_sub, map_mul, map_intCast, map_ofNat, conj_ofReal, conj_I, mul_neg,
    Int.cast_neg, neg_mul] using he'

/-- A loop in the closed lower half-plane that avoids zero has degree zero. -/
theorem loopDeg_eq_zero_of_im_nonpos (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hc : γ 0 = γ 1) (him : ∀ t, (γ t).im ≤ 0) : loopDeg γ hγ = 0 := by
  let δ : C(unitInterval, ℂ) := ⟨fun t => conj (γ t), continuous_conj.comp γ.continuous⟩
  have hδ : ∀ t, δ t ≠ 0 := fun t => by simpa [δ] using hγ t
  have hδc : δ 0 = δ 1 := by change conj (γ 0) = conj (γ 1); rw [hc]
  have hδim : ∀ t, 0 ≤ (δ t).im := fun t => by simpa [δ] using neg_nonneg.mpr (him t)
  have hz := loopDeg_eq_zero_of_im_nonneg δ hδ hδc hδim
  have he := loopDeg_conj γ hγ hc
  change loopDeg δ hδ = -loopDeg γ hγ at he
  rw [hz] at he
  exact neg_eq_zero.mp he.symm

/-- A loop with the side pattern of a reflected circle has degree negative one. -/
theorem loopDeg_eq_neg_one_of_reflected_circle (γ : C(unitInterval, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hc : γ 0 = γ 1) {r : ℝ} (hr : r ≠ 0)
    (hsign : ∀ t, (0 < (γ t).im ∧ 0 < (conj (circleLoop r t)).im) ∨
      ((γ t).im < 0 ∧ (conj (circleLoop r t)).im < 0) ∨
      (0 < (γ t).re ∧ 0 < (conj (circleLoop r t)).re) ∨
      ((γ t).re < 0 ∧ (conj (circleLoop r t)).re < 0)) :
    loopDeg γ hγ = -1 := by
  let δ : C(unitInterval, ℂ) := ⟨fun t => conj (circleLoop r t),
    continuous_conj.comp (circleLoop r).continuous⟩
  have hδ : ∀ t, δ t ≠ 0 := fun t => by simpa [δ] using circleLoop_ne_zero hr t
  have hδc : δ 0 = δ 1 := by
    change conj (circleLoop r 0) = conj (circleLoop r 1)
    rw [show circleLoop r 0 = circleLoop r 1 by
      simpa [circleLoop] using (periodic_circleMap 0 r 0).symm]
  have he := loopDeg_eq_of_coordinate_sign γ δ hγ hδ hc hδc hsign
  have hdeg := loopDeg_conj (circleLoop r) (circleLoop_ne_zero hr)
    (by simpa [circleLoop] using (periodic_circleMap 0 r 0).symm)
  rw [loopDeg_circle hr] at hdeg
  exact he.trans hdeg

private theorem circleLoop_im_pos {r : ℝ} (hr : 0 < r) (t : unitInterval)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1 / 2) :
    0 < (circleLoop r t).im := by
  change 0 < (circleMap 0 r (2 * Real.pi * (t : ℝ))).im
  rw [circleMap_zero_im]
  apply mul_pos hr (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · positivity
  · nlinarith [Real.pi_pos]

private theorem circleLoop_im_neg {r : ℝ} (hr : 0 < r) (t : unitInterval)
    (ht0 : 1 / 2 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (circleLoop r t).im < 0 := by
  change (circleMap 0 r (2 * Real.pi * (t : ℝ))).im < 0
  rw [circleMap_zero_im]
  have hs := Real.sin_pos_of_pos_of_lt_pi
    (x := 2 * Real.pi * (t : ℝ) - Real.pi) (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])
  rw [Real.sin_sub_pi] at hs
  exact mul_neg_of_pos_of_neg hr (neg_pos.mp hs)

private theorem circleLoop_im_eq_zero_of_boundary (r : ℝ) (t : unitInterval)
    (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1 / 2 ∨ (t : ℝ) = 1) :
    (circleLoop r t).im = 0 := by
  change (circleMap 0 r (2 * Real.pi * (t : ℝ))).im = 0
  rw [circleMap_zero_im]
  rcases ht with ht | ht | ht
  · rw [ht]; simp
  · rw [ht, show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring, Real.sin_pi, mul_zero]
  · rw [ht]; simp [Real.sin_two_pi]

/-- Each open semicircle occupies a preconnected parameter interval. -/
theorem circleLoop_im_preconnected {r : ℝ} (hr : 0 < r) :
    IsPreconnected {t : unitInterval | 0 < (circleLoop r t).im} ∧
      IsPreconnected {t : unitInterval | (circleLoop r t).im < 0} := by
  let m : unitInterval := ⟨1 / 2, by norm_num⟩
  have hp : {t : unitInterval | 0 < (circleLoop r t).im} = Set.Ioo 0 m := by
    ext t
    change 0 < (circleLoop r t).im ↔ 0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2
    constructor
    · intro ht
      have h0 : 0 < (t : ℝ) := by
        by_contra h
        have hz : (t : ℝ) = 0 := le_antisymm (not_lt.mp h) t.2.1
        have := circleLoop_im_eq_zero_of_boundary r t (Or.inl hz)
        linarith
      have h1 : (t : ℝ) < 1 / 2 := by
        by_contra h
        have hge : 1 / 2 ≤ (t : ℝ) := not_lt.mp h
        rcases eq_or_lt_of_le hge with he | he
        · have := circleLoop_im_eq_zero_of_boundary r t (Or.inr (Or.inl he.symm))
          linarith
        · rcases eq_or_lt_of_le t.2.2 with he' | he'
          · have := circleLoop_im_eq_zero_of_boundary r t (Or.inr (Or.inr he'))
            linarith
          · have := circleLoop_im_neg hr t he he'
            linarith
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      exact circleLoop_im_pos hr t h0 h1
  have hn : {t : unitInterval | (circleLoop r t).im < 0} = Set.Ioo m 1 := by
    ext t
    change (circleLoop r t).im < 0 ↔ 1 / 2 < (t : ℝ) ∧ (t : ℝ) < 1
    constructor
    · intro ht
      have h1 : (t : ℝ) < 1 := by
        by_contra h
        have hz : (t : ℝ) = 1 := le_antisymm t.2.2 (not_lt.mp h)
        have := circleLoop_im_eq_zero_of_boundary r t (Or.inr (Or.inr hz))
        linarith
      have h0 : 1 / 2 < (t : ℝ) := by
        by_contra h
        have hle : (t : ℝ) ≤ 1 / 2 := not_lt.mp h
        rcases eq_or_lt_of_le hle with he | he
        · have := circleLoop_im_eq_zero_of_boundary r t (Or.inr (Or.inl he))
          linarith
        · rcases eq_or_lt_of_le t.2.1 with he' | he'
          · have := circleLoop_im_eq_zero_of_boundary r t (Or.inl he'.symm)
            linarith
          · have := circleLoop_im_pos hr t he' he
            linarith
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      exact circleLoop_im_neg hr t h0 h1
  rw [hp, hn]
  exact ⟨isPreconnected_Ioo, isPreconnected_Ioo⟩

/-- A degree-one loop preserves the sides of a degree-one reference loop when the
preimages of the two open sides are connected and the axis signs agree. -/
theorem loop_im_sign_of_degree_one (γ δ : C(unitInterval, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hδ : ∀ t, δ t ≠ 0)
    (hγc : γ 0 = γ 1) (hδc : δ 0 = δ 1)
    (hγdeg : loopDeg γ hγ = 1) (hδdeg : loopDeg δ hδ = 1)
    (hpos : IsPreconnected {t | 0 < (δ t).im})
    (hneg : IsPreconnected {t | (δ t).im < 0})
    (haxis : ∀ t, (γ t).im = 0 ↔ (δ t).im = 0)
    (hre : ∀ t, (δ t).im = 0 →
      (0 < (γ t).re ∧ 0 < (δ t).re) ∨
      ((γ t).re < 0 ∧ (δ t).re < 0)) :
    (∀ t, 0 < (δ t).im → 0 < (γ t).im) ∧
      (∀ t, (δ t).im < 0 → (γ t).im < 0) := by
  have hcont : Continuous (fun t => (γ t).im) := Complex.continuous_im.comp γ.continuous
  have hp := hpos.mapsTo_Ioi_or_Iio hcont.continuousOn (b := 0)
    (fun t ht hz => (ne_of_gt ht) ((haxis t).mp hz))
  have hn := hneg.mapsTo_Ioi_or_Iio hcont.continuousOn (b := 0)
    (fun t ht hz => (ne_of_lt ht) ((haxis t).mp hz))
  rcases hp with hp | hp <;> rcases hn with hn | hn
  · have hnonneg : ∀ t, 0 ≤ (γ t).im := by
      intro t
      rcases lt_trichotomy (δ t).im 0 with h | h | h
      · exact le_of_lt (hn h)
      · exact le_of_eq ((haxis t).mpr h).symm
      · exact le_of_lt (hp h)
    have hz := loopDeg_eq_zero_of_im_nonneg γ hγ hγc hnonneg
    omega
  · exact ⟨fun t ht => hp ht, fun t ht => hn ht⟩
  · let η : C(unitInterval, ℂ) := ⟨fun t => conj (δ t),
      continuous_conj.comp δ.continuous⟩
    have hη : ∀ t, η t ≠ 0 := fun t => by simpa [η] using hδ t
    have hηc : η 0 = η 1 := by change conj (δ 0) = conj (δ 1); rw [hδc]
    have hsign : ∀ t, (0 < (γ t).im ∧ 0 < (η t).im) ∨
        ((γ t).im < 0 ∧ (η t).im < 0) ∨
        (0 < (γ t).re ∧ 0 < (η t).re) ∨
        ((γ t).re < 0 ∧ (η t).re < 0) := by
      intro t
      rcases lt_trichotomy (δ t).im 0 with h | h | h
      · left; exact ⟨hn h, by simpa [η] using neg_pos.mpr h⟩
      · rcases hre t h with hr | hr
        · exact Or.inr (Or.inr (Or.inl ⟨hr.1, by simpa [η] using hr.2⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hr.1, by simpa [η] using hr.2⟩))
      · right; left; exact ⟨hp h, by simpa [η] using neg_neg_of_pos h⟩
    have he := loopDeg_eq_of_coordinate_sign γ η hγ hη hγc hηc hsign
    have hc := loopDeg_conj δ hδ hδc
    change loopDeg η hη = -loopDeg δ hδ at hc
    omega
  · have hnonpos : ∀ t, (γ t).im ≤ 0 := by
      intro t
      rcases lt_trichotomy (δ t).im 0 with h | h | h
      · exact le_of_lt (hn h)
      · exact le_of_eq ((haxis t).mpr h)
      · exact le_of_lt (hp h)
    have hz := loopDeg_eq_zero_of_im_nonpos γ hγ hγc hnonpos
    omega

/-- A degree-one loop fixing the two axis points of a circle preserves its sides. -/
theorem loop_im_sign_of_circle (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hγc : γ 0 = γ 1) (hγdeg : loopDeg γ hγ = 1) {r : ℝ} (hr : 0 < r)
    (haxis : ∀ t, (γ t).im = 0 ↔ (circleLoop r t).im = 0)
    (hfix : ∀ t, (circleLoop r t).im = 0 → γ t = circleLoop r t) :
    (∀ t, 0 < (circleLoop r t).im → 0 < (γ t).im) ∧
      (∀ t, (circleLoop r t).im < 0 → (γ t).im < 0) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hc : circleLoop r 0 = circleLoop r 1 := by
    simpa [circleLoop] using (periodic_circleMap 0 r 0).symm
  have hre : ∀ t, (circleLoop r t).im = 0 →
      (0 < (γ t).re ∧ 0 < (circleLoop r t).re) ∨
      ((γ t).re < 0 ∧ (circleLoop r t).re < 0) := by
    intro t ht
    have hn : (circleLoop r t).re ≠ 0 := by
      intro hz
      have : circleLoop r t = 0 := Complex.ext (by simpa using hz) (by simpa using ht)
      exact circleLoop_ne_zero hr' t this
    rw [hfix t ht]
    rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inr ⟨h, h⟩
    · exact Or.inl ⟨h, h⟩
  exact loop_im_sign_of_degree_one γ (circleLoop r) hγ (circleLoop_ne_zero hr')
    hγc hc hγdeg (loopDeg_circle hr') (circleLoop_im_preconnected hr).1
    (circleLoop_im_preconnected hr).2 haxis hre

/-- A loop contained in a ball avoiding the origin has degree zero about the origin. -/
theorem loopDeg_add_const_of_norm_lt (q : ℂ) (γ : C(unitInterval, ℂ))
    (hc : γ 0 = γ 1) (hsmall : ∀ t, ‖γ t‖ < ‖q‖) :
    ∃ h : ∀ t, (ContinuousMap.const unitInterval q + γ) t ≠ 0,
      loopDeg (ContinuousMap.const unitInterval q + γ) h = 0 := by
  have hq : q ≠ 0 := by
    intro he
    have hh := hsmall 0
    simp only [he, norm_zero] at hh
    exact (not_lt_of_ge (norm_nonneg _)) hh
  have hne : ∀ t, (ContinuousMap.const unitInterval q + γ) t ≠ 0 := by
    intro t he
    have hnorm : ‖γ t‖ = ‖q‖ := by
      have : γ t = -q := by
        simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply,
          eq_neg_iff_add_eq_zero, add_comm] using he
      rw [this, norm_neg]
    exact (ne_of_lt (hsmall t)) hnorm
  refine ⟨hne, ?_⟩
  have heq := loopDeg_eq_of_norm_sub_lt
    (ContinuousMap.const unitInterval q + γ) (ContinuousMap.const unitInterval q)
    hne (fun _ => hq) (by simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, hc])
    rfl (fun t => by
      simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply, add_sub_cancel_left]
        using hsmall t)
  simpa only [loopDeg_const] using heq

/-- The recentered image of a loop under inversion. -/
def inversionLoop (q : ℂ) (γ : C(unitInterval, ℂ)) (h : ∀ t, q + γ t ≠ 0) :
    C(unitInterval, ℂ) where
  toFun t := (q + γ t)⁻¹ - q⁻¹
  continuous_toFun := ((continuous_const.add γ.continuous).inv₀ h).sub continuous_const

/-- Inversion preserves the degree of a loop in a ball avoiding the origin. -/
theorem loopDeg_inversionLoop (q : ℂ) (γ : C(unitInterval, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hc : γ 0 = γ 1) (hsmall : ∀ t, ‖γ t‖ < ‖q‖)
    (h : ∀ t, q + γ t ≠ 0) :
    ∃ hn : ∀ t, inversionLoop q γ h t ≠ 0,
      loopDeg (inversionLoop q γ h) hn = loopDeg γ hγ := by
  have hq : q ≠ 0 := by
    intro he
    have hh := hsmall 0
    simp only [he, norm_zero] at hh
    exact (not_lt_of_ge (norm_nonneg _)) hh
  let η : C(unitInterval, ℂ) := ContinuousMap.const unitInterval q + γ
  have hη : ∀ t, η t ≠ 0 := h
  have hηc : η 0 = η 1 := by
    change q + γ 0 = q + γ 1
    rw [hc]
  have hηdeg : loopDeg η hη = 0 := by
    obtain ⟨_, he⟩ := loopDeg_add_const_of_norm_lt q γ hc hsmall
    exact he
  let ν : C(unitInterval, ℂ) := ⟨fun t => (η t)⁻¹, η.continuous.inv₀ hη⟩
  have hν : ∀ t, ν t ≠ 0 := fun t => inv_ne_zero (hη t)
  have hνc : ν 0 = ν 1 := by change (η 0)⁻¹ = (η 1)⁻¹; rw [hηc]
  have hνdeg : loopDeg ν hν = 0 := by
    simpa only [hηdeg, neg_zero] using loopDeg_inv η hη hηc
  let κ : C(unitInterval, ℂ) := ContinuousMap.const unitInterval (-q⁻¹)
  have hκ : ∀ t, κ t ≠ 0 := fun _ => neg_ne_zero.mpr (inv_ne_zero hq)
  have hp : ∀ t, (κ * γ) t ≠ 0 := fun t => mul_ne_zero (hκ t) (hγ t)
  have hpc : (κ * γ) 0 = (κ * γ) 1 := by
    change -q⁻¹ * γ 0 = -q⁻¹ * γ 1
    rw [hc]
  have hprod := loopDeg_mul (κ * γ) ν hp hν hpc hνc
  have hleft := loopDeg_mul κ γ hκ hγ rfl hc
  have heq : inversionLoop q γ h = (κ * γ) * ν := by
    ext t
    change (q + γ t)⁻¹ - q⁻¹ = (-q⁻¹ * γ t) * (q + γ t)⁻¹
    field_simp [hq, h t]
    ring
  have hn : ∀ t, inversionLoop q γ h t ≠ 0 := by
    rw [heq]
    intro t
    exact mul_ne_zero (hp t) (hν t)
  refine ⟨hn, ?_⟩
  rw [hleft] at hprod
  have hκdeg : loopDeg κ hκ = 0 := loopDeg_const _ (neg_ne_zero.mpr (inv_ne_zero hq))
  have hresult : loopDeg (κ * γ * ν) (fun t => mul_ne_zero (hp t) (hν t)) =
      loopDeg γ hγ := by
    simpa only [hκdeg, hνdeg, zero_add, add_zero] using hprod
  simpa only [heq] using hresult

/-- Inversion preserves closure of recentered loops. -/
theorem inversionLoop_closed (q : ℂ) (γ : C(unitInterval, ℂ))
    (h : ∀ t, q + γ t ≠ 0) (hc : γ 0 = γ 1) :
    inversionLoop q γ h 0 = inversionLoop q γ h 1 := by
  change (q + γ 0)⁻¹ - q⁻¹ = (q + γ 1)⁻¹ - q⁻¹
  rw [hc]

/-- A chart, inversion, and another chart preserve the degree of a small loop. -/
theorem chart_inversion_chart_degree (first second : Source.OrientedChart)
    (a q b : ℂ) (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hc : γ 0 = γ 1) (hsmall : ∀ t, ‖first.mapLoop a γ t‖ < ‖q‖)
    (h : ∀ t, q + first.mapLoop a γ t ≠ 0) :
    ∃ hn : ∀ t, second.mapLoop b (inversionLoop q (first.mapLoop a γ) h) t ≠ 0,
      loopDeg (second.mapLoop b (inversionLoop q (first.mapLoop a γ) h)) hn =
        loopDeg γ hγ := by
  let δ := first.mapLoop a γ
  have hδ := first.mapLoop_ne_zero a γ hγ
  have hδc := first.mapLoop_closed a γ hc
  obtain ⟨hν, hνdeg⟩ := loopDeg_inversionLoop q δ hδ hδc hsmall h
  have hνc := inversionLoop_closed q δ h hδc
  refine ⟨second.mapLoop_ne_zero b (inversionLoop q δ h) hν, ?_⟩
  rw [second.mapLoop_degree b (inversionLoop q δ h) hν hνc, hνdeg]
  exact first.mapLoop_degree a γ hγ hc

/-- A small circle has degree one after a chart, inversion, and another chart. -/
theorem exists_chart_inversion_chart_circle (first second : Source.OrientedChart)
    (a q b : ℂ) (hq : q ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ (r : ℝ) (_hr : 0 < r)
      (h : ∀ t, q + first.mapLoop a (circleLoop r) t ≠ 0)
      (hn : ∀ t, second.mapLoop b (inversionLoop q (first.mapLoop a (circleLoop r)) h) t ≠ 0),
      r < R ∧ loopDeg (second.mapLoop b
        (inversionLoop q (first.mapLoop a (circleLoop r)) h)) hn = 1 := by
  obtain ⟨r, hr, hrR, hsmall⟩ := first.exists_small_mapLoop_circle a (norm_pos_iff.mpr hq) hR
  have hrc : circleLoop r 0 = circleLoop r 1 := by
    simpa [circleLoop] using (periodic_circleMap 0 r 0).symm
  have hfirstc := first.mapLoop_closed a (circleLoop r) hrc
  obtain ⟨h, _⟩ := loopDeg_add_const_of_norm_lt q (first.mapLoop a (circleLoop r)) hfirstc hsmall
  obtain ⟨hn, hdeg⟩ := chart_inversion_chart_degree first second a q b (circleLoop r)
    (circleLoop_ne_zero (ne_of_gt hr)) hrc hsmall h
  exact ⟨r, hr, h, hn, hrR, hdeg.trans (loopDeg_circle (ne_of_gt hr))⟩

/-- A chart-inversion-chart image of a small circle has degree one and small radius. -/
theorem exists_small_chart_inversion_chart_circle (first second : Source.OrientedChart)
    (a q : ℂ) (hq : q ≠ 0) {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    ∃ (r : ℝ) (_hr : 0 < r)
      (h : ∀ t, q + first.mapLoop a (circleLoop r) t ≠ 0)
      (hn : ∀ t, second.mapLoop q⁻¹ (inversionLoop q (first.mapLoop a (circleLoop r)) h) t ≠ 0),
      r < R ∧ loopDeg (second.mapLoop q⁻¹
        (inversionLoop q (first.mapLoop a (circleLoop r)) h)) hn = 1 ∧
        ∀ t, ‖second.mapLoop q⁻¹ (inversionLoop q (first.mapLoop a (circleLoop r)) h) t‖ < S := by
  let f : ℂ → ℂ := fun u => Complex.equivRealProdCLM.symm
    (second.map (Complex.equivRealProdCLM ((q + u)⁻¹)))
  have hinv : ContinuousAt (fun u : ℂ => (q + u)⁻¹) 0 := by
    apply ContinuousAt.inv₀ (continuousAt_const.add continuousAt_id)
    simpa using hq
  have hf : ContinuousAt f 0 := by
    apply (Complex.equivRealProdCLM.symm.continuous.comp
      (second.map.continuous.comp Complex.equivRealProdCLM.continuous)).continuousAt.comp hinv
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hf S hS
  have hmin : 0 < min δ ‖q‖ := lt_min hδ (norm_pos_iff.mpr hq)
  obtain ⟨r, hr, hrR, hsmall⟩ := first.exists_small_mapLoop_circle a hmin hR
  have hsmallq : ∀ t, ‖first.mapLoop a (circleLoop r) t‖ < ‖q‖ :=
    fun t => lt_of_lt_of_le (hsmall t) (min_le_right _ _)
  have hrc : circleLoop r 0 = circleLoop r 1 := by
    simpa [circleLoop] using (periodic_circleMap 0 r 0).symm
  obtain ⟨h, _⟩ := loopDeg_add_const_of_norm_lt q (first.mapLoop a (circleLoop r))
    (first.mapLoop_closed a (circleLoop r) hrc) hsmallq
  obtain ⟨hn, hdeg⟩ := chart_inversion_chart_degree first second a q q⁻¹ (circleLoop r)
    (circleLoop_ne_zero (ne_of_gt hr)) hrc hsmallq h
  refine ⟨r, hr, h, hn, hrR, hdeg.trans (loopDeg_circle (ne_of_gt hr)), ?_⟩
  intro t
  have hlt : dist (first.mapLoop a (circleLoop r) t) 0 < δ := by
    simpa using lt_of_lt_of_le (hsmall t) (min_le_left _ _)
  have hh := hδf hlt
  rw [dist_eq_norm] at hh
  change ‖Complex.equivRealProdCLM.symm
    (second.isotopy 1 (Complex.equivRealProdCLM
      (q⁻¹ + ((q + first.mapLoop a (circleLoop r) t)⁻¹ - q⁻¹)))) -
    Complex.equivRealProdCLM.symm (second.isotopy 1 (Complex.equivRealProdCLM q⁻¹))‖ < S
  rw [show second.isotopy 1 = second.map from second.finish]
  simpa [f] using hh

/-- The inverse of an oriented chart carries the inverse isotopy. -/
def Source.OrientedChart.symm (chart : Source.OrientedChart) : Source.OrientedChart where
  map := chart.map.symm
  isotopy := fun t => (chart.isotopy t).symm
  continuous := chart.inverse_continuous
  inverse_continuous := by simpa using chart.continuous
  start := by rw [chart.start]; rfl
  finish := by rw [chart.finish]

/-- The inverse chart preserves the winding degree of a recentered circle. -/
theorem Source.OrientedChart.inverse_isotopyCircle_degree (chart : Source.OrientedChart)
    (q : ℂ) {r : ℝ} (hr : r ≠ 0) :
    loopDeg (slice (chart.symm.isotopyCircle q r) 1)
      (fun t => chart.symm.isotopyCircle_ne_zero q hr (t, 1)) = 1 :=
  chart.symm.isotopyCircle_degree q hr

end
end FiniteAvalanches.Electrical
