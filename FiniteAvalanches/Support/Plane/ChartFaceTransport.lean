import FiniteAvalanches.Support.Plane.PuncturedTransport
import FiniteAvalanches.Support.Plane.ChartOrientation
import FiniteAvalanches.Support.Plane.LocalFaceIncidence

/-!
# Transport of oriented edge chart faces
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb
open Source Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- The coordinate formula uniquely determines punctured inversion. -/
theorem puncturedInversion_eq_of_formula (p : Plane)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (hformula : ∀ z, (c z).val =
      ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
       -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) :
    c = puncturedInversion p := by
  apply DFunLike.ext
  intro z
  apply Subtype.ext
  exact (hformula z).trans (puncturedInversion_apply p z).symm

/-- In complex coordinates, puncture transport is translated inversion. -/
theorem puncturedInversion_complex (p : Plane) (z : {z : Plane // z ≠ p}) :
    Complex.equivRealProdCLM.symm ((puncturedInversion p z).val) =
      (Complex.equivRealProdCLM.symm z.val - Complex.equivRealProdCLM.symm p)⁻¹ := by
  apply Complex.ext <;>
    simp [puncturedInversion_apply, Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
      sub_eq_add_neg, pow_two]

/-- A recentered chart-inversion-chart loop is the pointwise puncture transport. -/
theorem chart_inversion_chart_apply (first second : Source.OrientedChart)
    (a : ℂ) (p : Plane) (γ : C(unitInterval, ℂ))
    (h : ∀ t, (Complex.equivRealProdCLM.symm (first.map (Complex.equivRealProdCLM a)) -
      Complex.equivRealProdCLM.symm p) + first.mapLoop a γ t ≠ 0) (t : unitInterval) :
    ∃ hz : first.map (Complex.equivRealProdCLM (a + γ t)) ≠ p,
      second.mapLoop (Complex.equivRealProdCLM.symm
        (first.map (Complex.equivRealProdCLM a)) - Complex.equivRealProdCLM.symm p)⁻¹
        (inversionLoop (Complex.equivRealProdCLM.symm
          (first.map (Complex.equivRealProdCLM a)) - Complex.equivRealProdCLM.symm p)
          (first.mapLoop a γ) h) t =
      Complex.equivRealProdCLM.symm (second.map ((puncturedInversion p)
        ⟨first.map (Complex.equivRealProdCLM (a + γ t)), hz⟩).val) -
      Complex.equivRealProdCLM.symm (second.map (Complex.equivRealProdCLM
        (Complex.equivRealProdCLM.symm (first.map (Complex.equivRealProdCLM a)) -
          Complex.equivRealProdCLM.symm p)⁻¹)) := by
  let q : ℂ := Complex.equivRealProdCLM.symm (first.map (Complex.equivRealProdCLM a)) -
    Complex.equivRealProdCLM.symm p
  let z : Plane := first.map (Complex.equivRealProdCLM (a + γ t))
  have he : q + first.mapLoop a γ t =
      Complex.equivRealProdCLM.symm z - Complex.equivRealProdCLM.symm p := by
    rw [first.mapLoop_apply]
    dsimp [q, z]
    ring
  have hz : z ≠ p := by
    intro hz
    apply h t
    rw [he, hz, sub_self]
  refine ⟨hz, ?_⟩
  have hc := puncturedInversion_complex p ⟨z, hz⟩
  have hc' : ((puncturedInversion p) ⟨z, hz⟩).val =
      Complex.equivRealProdCLM ((q + first.mapLoop a γ t)⁻¹) := by
    rw [he]
    simpa [hc] using
      (Complex.equivRealProdCLM.apply_symm_apply ((puncturedInversion p) ⟨z, hz⟩).val).symm
  change second.mapLoop q⁻¹ (inversionLoop q (first.mapLoop a γ) h) t =
    Complex.equivRealProdCLM.symm (second.map ((puncturedInversion p) ⟨z, hz⟩).val) -
    Complex.equivRealProdCLM.symm (second.map (Complex.equivRealProdCLM q⁻¹))
  rw [second.mapLoop_apply, hc']
  simp only [inversionLoop, ContinuousMap.coe_mk, add_sub_cancel]

/-- An interior edge point has a neighborhood containing no vertices. -/
theorem Drawing.exists_ball_disjoint_vertices (D : Drawing J) (e : E)
    (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    ∃ r > 0, ∀ z ∈ Metric.ball (D.curve e t) r, z ∉ Set.range D.point := by
  have hclosed : IsClosed (Set.range D.point) := (Set.finite_range D.point).isClosed
  have hpoint : D.curve e t ∈ (Set.range D.point)ᶜ := by
    rintro ⟨v, hv⟩
    exact D.avoids e t ht0 ht1 v hv.symm
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl _ hpoint
  exact ⟨r, hr, fun z hz => hball hz⟩

/-- Curve transport identifies traces at points that avoid the vertex sets. -/
theorem Drawing.mem_trace_iff_of_curve_transport (D D' : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (hcurve : ∀ e t, D'.curve e t =
      (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val)
    (z : {z : Plane // z ≠ p}) (hz : z.val ∉ Set.range D.point)
    (hz' : (c z).val ∉ Set.range D'.point) :
    z.val ∈ drawingTrace D ↔ (c z).val ∈ drawingTrace D' := by
  constructor
  · rintro (h | h)
    · exact (hz h).elim
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp h
      right
      refine Set.mem_iUnion.mpr ⟨e, t, ?_⟩
      rw [hcurve]
      exact congrArg (fun x => (c x).val) (Subtype.ext ht)
  · rintro (h | h)
    · exact (hz' h).elim
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp h
      right
      refine Set.mem_iUnion.mpr ⟨e, t, ?_⟩
      rw [hcurve] at ht
      exact congrArg Subtype.val (c.injective (Subtype.ext ht))

private theorem EdgeChart.trace_axisBox (D : Drawing J) (e : E) (c : Source.EdgeChart D e)
    (z : Plane) (hz : z ∈ PlaneTopology.axisBox (1 / 2) c.radius) :
    c.chart.map.symm z ∈ drawingTrace D ↔ z.2 = 0 := by
  apply c.trace_box z
  · exact abs_lt.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  · exact abs_lt.mpr hz.2

/-- Points in the upper half of an edge chart lie in its positive face. -/
theorem EdgeChart.mem_positive_face (D : Drawing J) (e : E) (c : Source.EdgeChart D e)
    (z : Plane) (hx : |z.1 - 1 / 2| < c.radius) (hy : 0 < z.2)
    (hy' : z.2 < c.radius) :
    c.chart.map.symm z ∈ BSST.faceRegion D (BSST.positiveChartFace D e c) := by
  rw [BSST.positiveChartFace, faceRegion_mk]
  apply PlaneTopology.upper_half_box_subset_component (drawingTrace D) c.chart.map
    (1 / 2) c.radius c.radius_pos (EdgeChart.trace_axisBox D e c)
  exact ⟨z, ⟨⟨by linarith [(abs_lt.mp hx).1], by linarith [(abs_lt.mp hx).2]⟩,
    hy, hy'⟩, rfl⟩

/-- Points in the lower half of an edge chart lie in its negative face. -/
theorem EdgeChart.mem_negative_face (D : Drawing J) (e : E) (c : Source.EdgeChart D e)
    (z : Plane) (hx : |z.1 - 1 / 2| < c.radius) (hy : -c.radius < z.2)
    (hy' : z.2 < 0) :
    c.chart.map.symm z ∈ BSST.faceRegion D (BSST.negativeChartFace D e c) := by
  rw [BSST.negativeChartFace, faceRegion_mk]
  apply PlaneTopology.lower_half_box_subset_component (drawingTrace D) c.chart.map
    (1 / 2) c.radius c.radius_pos (EdgeChart.trace_axisBox D e c)
  exact ⟨z, ⟨⟨by linarith [(abs_lt.mp hx).1], by linarith [(abs_lt.mp hx).2]⟩,
    hy, hy'⟩, rfl⟩

/-- A sufficiently small ball around the chart midpoint contains no charted vertices. -/
theorem EdgeChart.exists_ball_disjoint_vertices (D : Drawing J) (e : E)
    (chart : Source.EdgeChart D e) :
    ∃ r > 0, ∀ z ∈ Metric.ball (1 / 2, 0) r,
      chart.chart.map.symm z ∉ Set.range D.point := by
  let vertices := Set.range (fun v => chart.chart.map (D.point v))
  have hclosed : IsClosed vertices := (Set.finite_range _).isClosed
  let mid : ArcParameter := ⟨1 / 2, by norm_num⟩
  have hmid : chart.chart.map (D.curve e mid) = (1 / 2, 0) := by
    apply chart.straight
    simpa [mid] using chart.radius_pos
  have hpoint : (1 / 2, 0) ∈ verticesᶜ := by
    rintro ⟨v, hv⟩
    have heq : D.point v = D.curve e mid := chart.chart.map.injective (hv.trans hmid.symm)
    exact D.avoids e mid (by norm_num [mid]) (by norm_num [mid]) v heq.symm
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl _ hpoint
  refine ⟨r, hr, ?_⟩
  intro z hz ⟨v, hv⟩
  apply hball hz
  exact ⟨v, by simpa using congrArg chart.chart.map hv⟩

/-- Inside vertex-free chart boxes, curve transport identifies the chart axes. -/
theorem EdgeChart.axis_iff_of_curve_transport (D D' : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (hcurve : ∀ e t, D'.curve e t =
      (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val)
    (e : E) (original : Source.EdgeChart D e) (transported : Source.EdgeChart D' e)
    (z : {z : Plane // z ≠ p}) (hz : z.val ∉ Set.range D.point)
    (hz' : (c z).val ∉ Set.range D'.point)
    (hx : |(original.chart.map z.val).1 - 1 / 2| < original.radius)
    (hy : |(original.chart.map z.val).2| < original.radius)
    (hx' : |(transported.chart.map (c z).val).1 - 1 / 2| < transported.radius)
    (hy' : |(transported.chart.map (c z).val).2| < transported.radius) :
    (original.chart.map z.val).2 = 0 ↔ (transported.chart.map (c z).val).2 = 0 := by
  have h₁ := original.trace_box (original.chart.map z.val) hx hy
  have h₂ := transported.trace_box (transported.chart.map (c z).val) hx' hy'
  simp only [Homeomorph.symm_apply_apply] at h₁ h₂
  exact h₁.symm.trans ((D.mem_trace_iff_of_curve_transport D' hp c hcurve z hz hz').trans h₂)

/-- Curve transport fixes the common chart coordinate along a short edge segment. -/
theorem EdgeChart.axis_fixed_of_curve_transport (D D' : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (hcurve : ∀ e t, D'.curve e t =
      (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val)
    (e : E) (original : Source.EdgeChart D e) (transported : Source.EdgeChart D' e)
    (x : ℝ) (hx : |x - 1 / 2| < original.radius)
    (hx' : |x - 1 / 2| < transported.radius)
    (z : {z : Plane // z ≠ p}) (hz : original.chart.map z.val = (x, 0)) :
    transported.chart.map (c z).val = (x, 0) := by
  have hbounds := abs_lt.mp hx
  have hx0 : 0 ≤ x := by linarith [original.radius_small]
  have hx1 : x ≤ 1 := by linarith [original.radius_small]
  let t : ArcParameter := ⟨x, hx0, hx1⟩
  have horig := original.straight t hx
  have hcurve_eq : D.curve e t = z.val := original.chart.map.injective (horig.trans hz.symm)
  have hcz : (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val = (c z).val :=
    congrArg (fun w => (c w).val) (Subtype.ext hcurve_eq)
  have htarget := transported.straight t hx'
  rw [hcurve, hcz] at htarget
  exact htarget

/-- Faces containing a common point are equal. -/
theorem face_eq_of_mem_faceRegion {D : Drawing J} {F G : BSST.Face D} {z : Plane}
    (hF : z ∈ BSST.faceRegion D F) (hG : z ∈ BSST.faceRegion D G) : F = G := by
  obtain ⟨_, hF⟩ := hF
  obtain ⟨_, hG⟩ := hG
  exact hF.symm.trans hG

/-- Side witnesses identify the corresponding faces under a punctured-plane transport. -/
theorem EdgeChart.faces_eq_of_side_witnesses (D D' : Drawing J) {p : Plane}
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (faces : BSST.Face D ≃ BSST.Face D')
    (hregion : ∀ F : BSST.Face D, ∀ z : {z : Plane // z ≠ p},
      z.val ∈ BSST.faceRegion D F ↔ (c z).val ∈ BSST.faceRegion D' (faces F))
    (e : E) (original : Source.EdgeChart D e) (transported : Source.EdgeChart D' e)
    (zPos zNeg : {z : Plane // z ≠ p})
    (hPos : |(original.chart.map zPos.val).1 - 1 / 2| < original.radius ∧
      0 < (original.chart.map zPos.val).2 ∧ (original.chart.map zPos.val).2 < original.radius)
    (hPos' : |(transported.chart.map (c zPos).val).1 - 1 / 2| < transported.radius ∧
      0 < (transported.chart.map (c zPos).val).2 ∧
      (transported.chart.map (c zPos).val).2 < transported.radius)
    (hNeg : |(original.chart.map zNeg.val).1 - 1 / 2| < original.radius ∧
      -original.radius < (original.chart.map zNeg.val).2 ∧ (original.chart.map zNeg.val).2 < 0)
    (hNeg' : |(transported.chart.map (c zNeg).val).1 - 1 / 2| < transported.radius ∧
      -transported.radius < (transported.chart.map (c zNeg).val).2 ∧
      (transported.chart.map (c zNeg).val).2 < 0) :
    faces (BSST.negativeChartFace D e original) = BSST.negativeChartFace D' e transported ∧
    faces (BSST.positiveChartFace D e original) = BSST.positiveChartFace D' e transported := by
  constructor
  · apply face_eq_of_mem_faceRegion
    · apply (hregion _ zNeg).mp
      simpa using EdgeChart.mem_negative_face D e original (original.chart.map zNeg.val)
        hNeg.1 hNeg.2.1 hNeg.2.2
    · simpa using EdgeChart.mem_negative_face D' e transported (transported.chart.map (c zNeg).val)
        hNeg'.1 hNeg'.2.1 hNeg'.2.2
  · apply face_eq_of_mem_faceRegion
    · apply (hregion _ zPos).mp
      simpa using EdgeChart.mem_positive_face D e original (original.chart.map zPos.val)
        hPos.1 hPos.2.1 hPos.2.2
    · simpa using EdgeChart.mem_positive_face D' e transported (transported.chart.map (c zPos).val)
        hPos'.1 hPos'.2.1 hPos'.2.2

/-- The midpoint of an edge has chart coordinate `(1/2, 0)`. -/
theorem EdgeChart.map_midpoint (D : Drawing J) (e : E) (chart : Source.EdgeChart D e) :
    chart.chart.map (D.curve e ⟨1 / 2, by norm_num⟩) = (1 / 2, 0) := by
  apply chart.straight
  simpa using chart.radius_pos

/-- Curve transport sends the original chart midpoint to the transported midpoint. -/
theorem EdgeChart.transport_midpoint (D D' : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (hcurve : ∀ e t, D'.curve e t =
      (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val)
    (e : E) (original : Source.EdgeChart D e) (transported : Source.EdgeChart D' e) :
    ∃ h : original.chart.map.symm (1 / 2, 0) ≠ p,
      transported.chart.map (c ⟨original.chart.map.symm (1 / 2, 0), h⟩).val =
        (1 / 2, 0) := by
  let mid : ArcParameter := ⟨1 / 2, by norm_num⟩
  have hm : original.chart.map.symm (1 / 2, 0) = D.curve e mid := by
    apply original.chart.map.injective
    simpa [mid] using (EdgeChart.map_midpoint D e original).symm
  have hn : original.chart.map.symm (1 / 2, 0) ≠ p :=
    hm ▸ curve_ne_of_not_mem_trace D hp e mid
  refine ⟨hn, ?_⟩
  have hcz : (c ⟨original.chart.map.symm (1 / 2, 0), hn⟩).val = D'.curve e mid := by
    rw [hcurve]
    exact congrArg (fun z => (c z).val) (Subtype.ext hm)
  rw [hcz]
  exact EdgeChart.map_midpoint D' e transported

/-- A complex displacement of norm less than `r` lies in the corresponding chart box. -/
theorem complex_mem_chart_box (w : ℂ) {r : ℝ} (hw : ‖w‖ < r) :
    |(Complex.equivRealProdCLM (⟨1 / 2, 0⟩ + w)).1 - 1 / 2| < r ∧
      |(Complex.equivRealProdCLM (⟨1 / 2, 0⟩ + w)).2| < r := by
  constructor
  · have h := Complex.abs_re_le_norm w
    change |((⟨1 / 2, 0⟩ : ℂ) + w).re - 1 / 2| < r
    simpa using lt_of_le_of_lt h hw
  · have h := Complex.abs_im_le_norm w
    change |((⟨1 / 2, 0⟩ : ℂ) + w).im| < r
    simpa using lt_of_le_of_lt h hw

/-- A complex displacement of norm less than `r` lies in the chart-coordinate ball. -/
theorem complex_mem_chart_ball (w : ℂ) {r : ℝ} (hw : ‖w‖ < r) :
    Complex.equivRealProdCLM (⟨1 / 2, 0⟩ + w) ∈ Metric.ball (1 / 2, 0) r := by
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  obtain ⟨h₁, h₂⟩ := complex_mem_chart_box w hw
  simpa [Real.dist_eq] using And.intro h₁ h₂

/-- A positive-radius standard circle has points on both sides of the axis. -/
theorem circleLoop_exists_sides {r : ℝ} (hr : 0 < r) :
    (∃ t, 0 < (QuantumZipper.CA.Topo.circleLoop r t).im) ∧
      ∃ t, (QuantumZipper.CA.Topo.circleLoop r t).im < 0 := by
  constructor
  · refine ⟨⟨1 / 4, by norm_num⟩, ?_⟩
    change 0 < (circleMap 0 r (2 * Real.pi * (1 / 4))).im
    rw [circleMap_zero_im, show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring,
      Real.sin_pi_div_two, mul_one]
    exact hr
  · refine ⟨⟨3 / 4, by norm_num⟩, ?_⟩
    change (circleMap 0 r (2 * Real.pi * (3 / 4))).im < 0
    rw [circleMap_zero_im,
      show 2 * Real.pi * (3 / 4) = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two]
    linarith

/-- Every point of a standard circle has norm equal to its nonnegative radius. -/
theorem circleLoop_norm {r : ℝ} (hr : 0 ≤ r) (t : unitInterval) :
    ‖QuantumZipper.CA.Topo.circleLoop r t‖ = r := by
  change ‖circleMap 0 r (2 * Real.pi * (t : ℝ))‖ = r
  rw [norm_circleMap_zero, abs_of_nonneg hr]

open QuantumZipper.CA.Topo in
/-- A small, orientation-preserving circle identifies both chart faces. -/
theorem EdgeChart.faces_eq_of_circle (D D' : Drawing J) {p : Plane}
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (faces : BSST.Face D ≃ BSST.Face D')
    (hregion : ∀ F : BSST.Face D, ∀ z : {z : Plane // z ≠ p},
      z.val ∈ BSST.faceRegion D F ↔ (c z).val ∈ BSST.faceRegion D' (faces F))
    (e : E) (original : Source.EdgeChart D e) (transported : Source.EdgeChart D' e)
    (r : ℝ) (hr : 0 < r) (hradius : r < original.radius)
    (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hclosed : γ 0 = γ 1) (hdeg : loopDeg γ hγ = 1)
    (hsmall : ∀ t, ‖γ t‖ < transported.radius)
    (haxis : ∀ t, (γ t).im = 0 ↔ (circleLoop r t).im = 0)
    (hfix : ∀ t, (circleLoop r t).im = 0 → γ t = circleLoop r t)
    (hpoints : ∀ t, ∃ z : {z : Plane // z ≠ p},
      original.chart.map z.val = Complex.equivRealProdCLM (⟨1 / 2, 0⟩ + circleLoop r t) ∧
      transported.chart.map (c z).val = Complex.equivRealProdCLM (⟨1 / 2, 0⟩ + γ t)) :
    faces (BSST.negativeChartFace D e original) = BSST.negativeChartFace D' e transported ∧
    faces (BSST.positiveChartFace D e original) = BSST.positiveChartFace D' e transported := by
  have hsides := loop_im_sign_of_circle γ hγ hclosed hdeg hr haxis hfix
  obtain ⟨⟨tp, hp⟩, ⟨tn, hn⟩⟩ := circleLoop_exists_sides hr
  obtain ⟨zp, hzp, hzp'⟩ := hpoints tp
  obtain ⟨zn, hzn, hzn'⟩ := hpoints tn
  have hboxp := complex_mem_chart_box (circleLoop r tp) (by rw [circleLoop_norm hr.le]; exact hradius)
  have hboxn := complex_mem_chart_box (circleLoop r tn) (by rw [circleLoop_norm hr.le]; exact hradius)
  have hboxp' := complex_mem_chart_box (γ tp) (hsmall tp)
  have hboxn' := complex_mem_chart_box (γ tn) (hsmall tn)
  apply EdgeChart.faces_eq_of_side_witnesses D D' c faces hregion e original transported zp zn
  · rw [hzp]
    have h := (abs_lt.mp hboxp.2).2
    exact ⟨hboxp.1, by simpa using hp, h⟩
  · rw [hzp']
    have h := (abs_lt.mp hboxp'.2).2
    exact ⟨hboxp'.1, by simpa using hsides.1 tp hp, h⟩
  · rw [hzn]
    have h := (abs_lt.mp hboxn.2).1
    exact ⟨hboxn.1, h, by simpa using hn⟩
  · rw [hzn']
    have h := (abs_lt.mp hboxn'.2).1
    exact ⟨hboxn'.1, h, by simpa using hsides.2 tn hn⟩

open QuantumZipper.CA.Topo in
/-- Holomorphic puncture transport preserves both oriented chart faces. -/
theorem Drawing.punctured_chart_face_transport (D D' : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (hformula : ∀ z, (c z).val =
      ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
       -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2)))
    (hcurve : ∀ e t, D'.curve e t =
      (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val)
    (faces : BSST.Face D ≃ BSST.Face D')
    (hregion : ∀ F : BSST.Face D, ∀ z : {z : Plane // z ≠ p},
      z.val ∈ BSST.faceRegion D F ↔ (c z).val ∈ BSST.faceRegion D' (faces F))
    (e : E) (original : Source.EdgeChart D e) (transported : Source.EdgeChart D' e) :
    faces (BSST.negativeChartFace D e original) = BSST.negativeChartFace D' e transported ∧
    faces (BSST.positiveChartFace D e original) = BSST.positiveChartFace D' e transported := by
  have hc := puncturedInversion_eq_of_formula p c hformula
  subst c
  obtain ⟨hm, hmid⟩ := EdgeChart.transport_midpoint D D' hp (puncturedInversion p)
    hcurve e original transported
  let first := original.chart.symm
  let second := transported.chart
  let a : ℂ := ⟨1 / 2, 0⟩
  let q : ℂ := Complex.equivRealProdCLM.symm (first.map (Complex.equivRealProdCLM a)) -
    Complex.equivRealProdCLM.symm p
  have hq : q ≠ 0 := by
    intro hz
    apply hm
    apply Complex.equivRealProdCLM.symm.injective
    have h := sub_eq_zero.mp hz
    simpa [q, first, Source.OrientedChart.symm, a] using h
  have hcenter : second.map (Complex.equivRealProdCLM q⁻¹) = (1 / 2, 0) := by
    have h := puncturedInversion_complex p ⟨original.chart.map.symm (1 / 2, 0), hm⟩
    have heq : Complex.equivRealProdCLM q⁻¹ =
        ((puncturedInversion p) ⟨original.chart.map.symm (1 / 2, 0), hm⟩).val := by
      apply Complex.equivRealProdCLM.symm.injective
      have ha : Complex.equivRealProdCLM a = (1 / 2, 0) := rfl
      simpa only [q, first, Source.OrientedChart.symm, ha,
        ContinuousLinearEquiv.symm_apply_apply] using h.symm
    simpa [second, heq] using hmid
  obtain ⟨R, hR, hRvertices⟩ := EdgeChart.exists_ball_disjoint_vertices D e original
  obtain ⟨S, hS, hSvertices⟩ := EdgeChart.exists_ball_disjoint_vertices D' e transported
  obtain ⟨r, hr, h, hn, hrsmall, hdeg, hsmall⟩ :=
    exists_small_chart_inversion_chart_circle first second a q hq
      (lt_min original.radius_pos (lt_min transported.radius_pos hR))
      (lt_min transported.radius_pos hS)
  let γ := second.mapLoop q⁻¹ (inversionLoop q (first.mapLoop a (circleLoop r)) h)
  have hclosed : γ 0 = γ 1 := by
    have hcircle : circleLoop r 0 = circleLoop r 1 := by
      simpa [circleLoop] using (periodic_circleMap 0 r 0).symm
    apply second.mapLoop_closed
    change (q + first.mapLoop a (circleLoop r) 0)⁻¹ - q⁻¹ =
      (q + first.mapLoop a (circleLoop r) 1)⁻¹ - q⁻¹
    rw [first.mapLoop_closed a (circleLoop r) hcircle]
  have hpoints : ∀ t, ∃ z : {z : Plane // z ≠ p},
      original.chart.map z.val = Complex.equivRealProdCLM (a + circleLoop r t) ∧
      transported.chart.map ((puncturedInversion p) z).val =
        Complex.equivRealProdCLM (a + γ t) := by
    intro t
    obtain ⟨hz, hz'⟩ := chart_inversion_chart_apply first second a p (circleLoop r) h t
    refine ⟨⟨first.map (Complex.equivRealProdCLM (a + circleLoop r t)), hz⟩, ?_, ?_⟩
    · simp [first, Source.OrientedChart.symm]
    · apply Complex.equivRealProdCLM.symm.injective
      have hcenter' : Complex.equivRealProdCLM.symm
          (second.map (Complex.equivRealProdCLM q⁻¹)) = a := by
        rw [hcenter]
        rfl
      change Complex.equivRealProdCLM.symm
        (second.map ((puncturedInversion p) ⟨first.map
          (Complex.equivRealProdCLM (a + circleLoop r t)), hz⟩).val) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
      change γ t = _ at hz'
      rw [hcenter'] at hz'
      exact (eq_sub_iff_add_eq.mp hz').symm.trans (add_comm _ _)
  have haxis : ∀ t, (γ t).im = 0 ↔ (circleLoop r t).im = 0 := by
    intro t
    obtain ⟨z, hz, hz'⟩ := hpoints t
    have hw : ‖circleLoop r t‖ < R := by
      rw [circleLoop_norm hr.le]
      exact lt_of_lt_of_le hrsmall (le_trans (min_le_right _ _) (min_le_right _ _))
    have hw' : ‖γ t‖ < S := lt_of_lt_of_le (hsmall t) (min_le_right _ _)
    have hb := complex_mem_chart_box (circleLoop r t)
      (by rw [circleLoop_norm hr.le]; exact lt_of_lt_of_le hrsmall (min_le_left _ _))
    have hb' := complex_mem_chart_box (γ t)
      (lt_of_lt_of_le (hsmall t) (min_le_left _ _))
    have hv : z.val ∉ Set.range D.point := by
      have hbz : original.chart.map z.val ∈ Metric.ball (1 / 2, 0) R := by
        rw [hz]; exact complex_mem_chart_ball _ hw
      simpa using hRvertices (original.chart.map z.val) hbz
    have hv' : ((puncturedInversion p) z).val ∉ Set.range D'.point := by
      have hbz : transported.chart.map ((puncturedInversion p) z).val ∈
          Metric.ball (1 / 2, 0) S := by
        rw [hz']; exact complex_mem_chart_ball _ hw'
      simpa using hSvertices _ hbz
    have hiff := EdgeChart.axis_iff_of_curve_transport D D' hp (puncturedInversion p)
      hcurve e original transported z hv hv' (by simpa [hz, a] using hb.1)
      (by simpa [hz, a] using hb.2) (by simpa [hz', a] using hb'.1) (by simpa [hz', a] using hb'.2)
    simpa [hz, hz', a] using hiff.symm
  have hfix : ∀ t, (circleLoop r t).im = 0 → γ t = circleLoop r t := by
    intro t ht
    obtain ⟨z, hz, hz'⟩ := hpoints t
    have hb := complex_mem_chart_box (circleLoop r t)
      (by rw [circleLoop_norm hr.le]; exact lt_of_lt_of_le hrsmall (min_le_left _ _))
    have hb' := complex_mem_chart_box (γ t)
      (lt_of_lt_of_le (hsmall t) (min_le_left _ _))
    have hreal : original.chart.map z.val = ((a + circleLoop r t).re, 0) := by
      rw [hz]
      ext <;> simp [a, ht]
    have hx' : |(a + circleLoop r t).re - 1 / 2| < transported.radius := by
      have hx := complex_mem_chart_box (circleLoop r t) (r := transported.radius)
        (by rw [circleLoop_norm hr.le];
            exact lt_of_lt_of_le hrsmall (le_trans (min_le_right _ _) (min_le_left _ _)))
      simpa [a] using hx.1
    have hfixed := EdgeChart.axis_fixed_of_curve_transport D D' hp (puncturedInversion p)
      hcurve e original transported _ (by simpa [hz, a] using hb.1) hx' z hreal
    have heq : Complex.equivRealProdCLM (a + γ t) =
        Complex.equivRealProdCLM (a + circleLoop r t) := by
      rw [← hz', hfixed]
      ext <;> simp [a, ht]
    have := Complex.equivRealProdCLM.injective heq
    exact add_left_cancel this
  exact EdgeChart.faces_eq_of_circle D D' (puncturedInversion p) faces hregion e original
    transported r hr (lt_of_lt_of_le hrsmall (min_le_left _ _)) γ hn hclosed hdeg
    (fun t => lt_of_lt_of_le (hsmall t) (min_le_left _ _)) haxis hfix hpoints


end FiniteAvalanches.Electrical.StatementGeometry
