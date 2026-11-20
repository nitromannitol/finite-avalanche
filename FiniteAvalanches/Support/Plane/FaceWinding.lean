import FiniteAvalanches.Support.Plane.EdgeCrossingPaths
import FiniteAvalanches.Support.Plane.HorizontalCrossingDegree
import FiniteAvalanches.Support.Plane.ChartOrientation
import FiniteAvalanches.Support.Plane.PuncturedTransport

/-!
# Winding numbers of closed paths in a drawing

A closed path inside the trace of a plane drawing has a winding number around
every point off the trace, constant on each face. Across an edge, at its
oriented chart, the winding number on the positive side exceeds the one on the
negative side by the signed passage of the path through the midpoint of the
edge. The computation transports the path by the chart, which is isotopic to
the identity and so preserves winding numbers.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open QuantumZipper.CA.Topo
open FiniteAvalanches.Electrical
open Source BSST Complex Set

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- A closed plane path in complex coordinates. -/
noncomputable def complexLoop {a : ℝ × ℝ} (P : Path a a) : C(unitInterval, ℂ) :=
  ⟨fun t => Complex.equivRealProdCLM.symm (P t),
    Complex.equivRealProdCLM.symm.continuous.comp P.continuous⟩

theorem complexLoop_closed {a : ℝ × ℝ} (P : Path a a) : complexLoop P 0 = complexLoop P 1 := by
  simp [complexLoop]

theorem complexLoop_ne {a z : ℝ × ℝ} (P : Path a a) (hz : z ∉ range P) (t : unitInterval) :
    complexLoop P t ≠ Complex.equivRealProdCLM.symm z := by
  intro h
  exact hz ⟨t, Complex.equivRealProdCLM.symm.injective h⟩

/-- The winding number of a closed plane path around a point off its range. -/
noncomputable def windingAround {a : ℝ × ℝ} (P : Path a a) (z : ℝ × ℝ) (hz : z ∉ range P) : ℤ :=
  loopDeg (complexLoop P - ContinuousMap.const unitInterval (Complex.equivRealProdCLM.symm z))
    (fun t => sub_ne_zero.mpr (complexLoop_ne P hz t))

/-- The winding number of a closed path is constant on a connected set off its range. -/
theorem windingAround_eq_of_isPreconnected {a : ℝ × ℝ} (P : Path a a) {S : Set (ℝ × ℝ)}
    (hS : IsPreconnected S) (hSP : Disjoint S (range P)) {z w : ℝ × ℝ} (hz : z ∈ S)
    (hw : w ∈ S) :
    windingAround P z (disjoint_left.mp hSP hz) = windingAround P w (disjoint_left.mp hSP hw) := by
  unfold windingAround
  have hz' : Complex.equivRealProdCLM.symm z ∉ range (complexLoop P) := by
    rintro ⟨t, ht⟩
    exact complexLoop_ne P (disjoint_left.mp hSP hz) t ht
  have hmem : Complex.equivRealProdCLM.symm w ∈
      connectedComponentIn (range (complexLoop P))ᶜ (Complex.equivRealProdCLM.symm z) := by
    apply (hS.image _ Complex.equivRealProdCLM.symm.continuous.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem _ hz)
    · rintro _ ⟨u, hu, rfl⟩ ⟨t, ht⟩
      exact complexLoop_ne P (disjoint_left.mp hSP hu) t ht
    · exact mem_image_of_mem _ hw
  exact loopDeg_sub_const_eq_of_connectedComponentIn (complexLoop P) (complexLoop_closed P) hz' hmem

/-- Points of a face region lie off the trace. -/
theorem not_mem_trace_of_mem_faceRegion {D : Drawing J} {F : Face D} {z : ℝ × ℝ}
    (hz : z ∈ faceRegion D F) : z ∉ drawingTrace D := hz.1

/-- The winding number of a closed path in the trace around a face. -/
noncomputable def faceWinding (D : Drawing J) {a : ℝ × ℝ} (P : Path a a)
    (hP : range P ⊆ drawingTrace D) (F : Face D) : ℤ :=
  windingAround P (faceRegion_nonempty D F).some
    (fun h => not_mem_trace_of_mem_faceRegion (faceRegion_nonempty D F).some_mem (hP h))

/-- The face winding number is the winding number around any point of the face. -/
theorem faceWinding_eq (D : Drawing J) {a : ℝ × ℝ} (P : Path a a)
    (hP : range P ⊆ drawingTrace D) {F : Face D} {z : ℝ × ℝ} (hz : z ∈ faceRegion D F) :
    faceWinding D P hP F = windingAround P z (fun h => not_mem_trace_of_mem_faceRegion hz (hP h)) :=
  windingAround_eq_of_isPreconnected P (faceRegion_isConnected D F).isPreconnected
    (disjoint_left.mpr fun _ hu hr => not_mem_trace_of_mem_faceRegion hu (hP hr))
    (faceRegion_nonempty D F).some_mem hz

/-- Winding numbers on the two sides of an edge chart differ by the signed
passage of the closed path through the midpoint of the edge. -/
theorem windingAround_chart_sides (D : Drawing J) {a : ℝ × ℝ} (P : Path a a)
    (hP : range P ⊆ drawingTrace D) (e : E) (c : EdgeChart D e) {σ : ℤ}
    (hσ : EdgeCrossingSign D e P σ) :
    windingAround P (c.chart.map.symm (1 / 2, c.radius / 2))
        (fun h => positive_chart_point_off_trace D e c (hP h)) =
      windingAround P (c.chart.map.symm (1 / 2, -(c.radius / 2)))
        (fun h => negative_chart_point_off_trace D e c (hP h)) + σ := by
  have hr := c.radius_pos
  have hr4 := c.radius_small
  let β : C(unitInterval, ℂ) := ⟨fun t => Complex.equivRealProdCLM.symm (c.chart.map (P t)),
    Complex.equivRealProdCLM.symm.continuous.comp (c.chart.map.continuous.comp P.continuous)⟩
  have hβ : ∀ t, β t = Complex.equivRealProdCLM.symm (c.chart.map (P t)) := fun t => rfl
  have hβc : β 0 = β 1 := by simp [hβ]
  have hpt : ∀ (t : unitInterval) (y : ℝ), β t = ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I →
      P t = c.chart.map.symm (1 / 2, y) := by
    intro t y h
    have h' : c.chart.map (P t) = (1 / 2, y) := by
      apply Complex.equivRealProdCLM.symm.injective
      rw [← hβ, h, Complex.equivRealProdCLM_symm_apply]
    rw [← h', c.chart.map.symm_apply_apply]
  have hside : ∀ (y : ℝ) (hy : c.chart.map.symm (1 / 2, y) ∉ range P),
      windingAround P (c.chart.map.symm (1 / 2, y)) hy =
        loopDeg (β - ContinuousMap.const unitInterval (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
          (fun t => by
            rw [ContinuousMap.sub_apply, ContinuousMap.const_apply, sub_ne_zero]
            exact fun h => hy ⟨t, hpt t y h⟩) := by
    intro y hy
    have hne : ∀ t, complexLoop P t ≠
        Complex.equivRealProdCLM.symm (c.chart.map.symm (1 / 2, y)) := complexLoop_ne P hy
    have hdeg := c.chart.isotopyLoop_degree
      (Complex.equivRealProdCLM.symm (c.chart.map.symm (1 / 2, y))) (complexLoop P) hne
      (complexLoop_closed P)
    unfold windingAround
    rw [← hdeg]
    apply loopDeg_congr
    ext t
    change Complex.equivRealProdCLM.symm (c.chart.isotopy 1
        (Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm (P t)))) -
      Complex.equivRealProdCLM.symm (c.chart.isotopy 1 (Complex.equivRealProdCLM
        (Complex.equivRealProdCLM.symm (c.chart.map.symm (1 / 2, y))))) =
      β t - (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)
    rw [show c.chart.isotopy 1 = c.chart.map from c.chart.finish,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
      Homeomorph.apply_symm_apply, Complex.equivRealProdCLM_symm_apply (1 / 2, y), ← hβ]
  rw [hside, hside]
  have hmid : c.chart.map (D.curve e halfParameter) = (1 / 2, 0) := by
    have := c.straight halfParameter (by simp [halfParameter, hr])
    simpa [halfParameter] using this
  have hβre : ∀ t, β t = ((c.chart.map (P t)).1 : ℂ) + ((c.chart.map (P t)).2 : ℂ) * I :=
    fun t => Complex.equivRealProdCLM_symm_apply _
  have hseg : ∀ t, (β t).re = 1 / 2 → |(β t).im| < c.radius / 2 →
      P t = D.curve e halfParameter := by
    intro t hre him
    have hre' : (c.chart.map (P t)).1 = 1 / 2 := by simpa [hβre] using hre
    have him' : |(c.chart.map (P t)).2| < c.radius / 2 := by simpa [hβre] using him
    have hbox := c.trace_box (c.chart.map (P t)) (by rw [hre']; simp [hr])
      (by linarith)
    rw [c.chart.map.symm_apply_apply] at hbox
    have hy : (c.chart.map (P t)).2 = 0 := hbox.mp (hP ⟨t, rfl⟩)
    apply c.chart.map.injective
    rw [hmid]
    exact Prod.ext hre' hy
  have hup : ∀ t, β t ≠ ((1 / 2 : ℝ) : ℂ) + ((c.radius / 2 : ℝ) : ℂ) * I := by
    intro t h
    apply positive_chart_point_off_trace D e c
    rw [← hpt t _ h]
    exact hP ⟨t, rfl⟩
  have hlow : ∀ t, β t ≠ ((1 / 2 : ℝ) : ℂ) - ((c.radius / 2 : ℝ) : ℂ) * I := by
    intro t h
    apply negative_chart_point_off_trace D e c
    rw [← hpt t (-(c.radius / 2)) (by rw [h]; push_cast; ring)]
    exact hP ⟨t, rfl⟩
  have hconst : β - ContinuousMap.const unitInterval
        (((1 / 2 : ℝ) : ℂ) + ((-(c.radius / 2) : ℝ) : ℂ) * I) =
      β - ContinuousMap.const unitInterval
        (((1 / 2 : ℝ) : ℂ) - ((c.radius / 2 : ℝ) : ℂ) * I) := by
    congr 2
    push_cast
    ring
  rw [loopDeg_congr hconst _ (fun t => sub_ne_zero.mpr (hlow t))]
  rcases hσ with ⟨rfl, hav⟩ | ⟨hσ, t₀, h0, h1, huniq, ε, hε, κ, hκ, hloc⟩
  · exact loopDeg_upper_eq_lower_add_of_crossing β hβc (half_pos hr) hup hlow 0
      (Or.inl rfl) 0 (fun t hre him => (hav t (hseg t hre him)).elim)
      (fun h => (h rfl).elim)
  · refine loopDeg_upper_eq_lower_add_of_crossing β hβc (half_pos hr) hup hlow σ
      (Or.inr hσ) t₀ (fun t hre him => ⟨by rcases hσ with h | h <;> simp [h],
        huniq t (hseg t hre him)⟩) (fun _ => ?_)
    refine ⟨h0, h1, min ε (c.radius / (2 * κ)), lt_min hε (by positivity), κ, hκ, ?_⟩
    intro t ht
    have ht1 := lt_of_lt_of_le ht (min_le_left _ _)
    have ht2 := lt_of_lt_of_le ht (min_le_right _ _)
    have hσabs : |(σ : ℝ)| = 1 := by rcases hσ with h | h <;> simp [h]
    have hdist : |(σ : ℝ) * κ * ((t : ℝ) - t₀)| < c.radius / 2 := by
      rw [abs_mul, abs_mul, hσabs, abs_of_pos hκ, one_mul]
      calc κ * |(t : ℝ) - t₀| < κ * (c.radius / (2 * κ)) := mul_lt_mul_of_pos_left ht2 hκ
        _ = c.radius / 2 := by field_simp
    rw [abs_lt] at hdist
    have hs0 : 0 ≤ 1 / 2 + (σ : ℝ) * κ * ((t : ℝ) - t₀) := by linarith
    have hs1 : 1 / 2 + (σ : ℝ) * κ * ((t : ℝ) - t₀) ≤ 1 := by linarith
    rw [hβ, hloc t ht1, projIcc_of_mem _ ⟨hs0, hs1⟩]
    have hst := c.straight ⟨1 / 2 + (σ : ℝ) * κ * ((t : ℝ) - t₀), hs0, hs1⟩ (by
      simp only
      rw [abs_lt]
      constructor <;> linarith)
    rw [hst, Complex.equivRealProdCLM_symm_apply]
    simp

/-- Face winding numbers on the two sides of an edge chart differ by the signed
passage of the closed path through the midpoint of the edge. -/
theorem faceWinding_chart_sides (D : Drawing J) {a : ℝ × ℝ} (P : Path a a)
    (hP : range P ⊆ drawingTrace D) (e : E) (c : EdgeChart D e) {σ : ℤ}
    (hσ : EdgeCrossingSign D e P σ) :
    faceWinding D P hP (positiveChartFace D e c) =
      faceWinding D P hP (negativeChartFace D e c) + σ := by
  rw [faceWinding_eq D P hP (F := positiveChartFace D e c)
      (z := c.chart.map.symm (1 / 2, c.radius / 2)) ⟨positive_chart_point_off_trace D e c, rfl⟩,
    faceWinding_eq D P hP (F := negativeChartFace D e c)
      (z := c.chart.map.symm (1 / 2, -(c.radius / 2)))
      ⟨negative_chart_point_off_trace D e c, rfl⟩]
  exact windingAround_chart_sides D P hP e c hσ

end FiniteAvalanches.Electrical.StatementGeometry
