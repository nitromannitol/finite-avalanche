import FiniteAvalanches.Electrical.SplitStep.OriginalPhysicalCopy
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

private theorem component_cast_equal (S T : Set Plane) (h : S = T)
    (x y : Plane) (hs : x ∉ S) (ht : y ∉ T) (hxy : x = y) :
    Equiv.cast (congrArg (fun U : Set Plane => ConnectedComponents {w : Plane // w ∉ U}) h)
      (ConnectedComponents.mk (⟨x, hs⟩ : {w : Plane // w ∉ S})) =
    ConnectedComponents.mk (⟨y, ht⟩ : {w : Plane // w ∉ T}) := by
  cases h
  cases hxy
  rfl

/-- Rotation about the midpoint used by edge charts. -/
def chartRotation (a : ℝ) : Plane ≃ₜ Plane where
  toFun z := (Real.cos a * (z.1 - 1/2) - Real.sin a * z.2 + 1/2,
    Real.sin a * (z.1 - 1/2) + Real.cos a * z.2)
  invFun z := (Real.cos a * (z.1 - 1/2) + Real.sin a * z.2 + 1/2,
    -Real.sin a * (z.1 - 1/2) + Real.cos a * z.2)
  left_inv := by
    intro z
    apply Prod.ext
    · dsimp
      linear_combination (z.1 - 1/2) * Real.cos_sq_add_sin_sq a
    · dsimp
      linear_combination z.2 * Real.cos_sq_add_sin_sq a
  right_inv := by
    intro z
    apply Prod.ext
    · dsimp
      linear_combination (z.1 - 1/2) * Real.cos_sq_add_sin_sq a
    · dsimp
      linear_combination z.2 * Real.cos_sq_add_sin_sq a
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The half turn has an explicit isotopy and therefore preserves planar orientation. -/
def chartHalfTurn : OrientedChart where
  map := chartRotation Real.pi
  isotopy t := chartRotation (Real.pi * t.val)
  continuous := by change Continuous (fun p : ArcParameter × Plane =>
    (Real.cos (Real.pi * p.1.val) * (p.2.1 - 1/2) - Real.sin (Real.pi * p.1.val) * p.2.2 + 1/2,
      Real.sin (Real.pi * p.1.val) * (p.2.1 - 1/2) + Real.cos (Real.pi * p.1.val) * p.2.2)); fun_prop
  inverse_continuous := by change Continuous (fun p : ArcParameter × Plane =>
    (Real.cos (Real.pi * p.1.val) * (p.2.1 - 1/2) + Real.sin (Real.pi * p.1.val) * p.2.2 + 1/2,
      -Real.sin (Real.pi * p.1.val) * (p.2.1 - 1/2) + Real.cos (Real.pi * p.1.val) * p.2.2)); fun_prop
  start := by ext z <;> simp [chartRotation]
  finish := by simp only [mul_one]

theorem chart_half_turn_apply (z : Plane) : chartHalfTurn.map z = (1 - z.1, -z.2) := by
  apply Prod.ext
  · simp [chartHalfTurn, chartRotation]
    ring
  · simp [chartHalfTurn, chartRotation]

theorem chart_half_turn_symm_apply (z : Plane) : chartHalfTurn.map.symm z = (1 - z.1, -z.2) := by
  apply Prod.ext
  · simp [chartHalfTurn, chartRotation]
    ring
  · simp [chartHalfTurn, chartRotation]

/-- Composition of actual charts carries the two isotopies along the same interval. -/
def composeOrientedChart (c d : OrientedChart) : OrientedChart where
  map := c.map.trans d.map
  isotopy t := (c.isotopy t).trans (d.isotopy t)
  continuous := d.continuous.comp (continuous_fst.prodMk c.continuous)
  inverse_continuous := c.inverse_continuous.comp (continuous_fst.prodMk d.inverse_continuous)
  start := by rw [c.start, d.start]; rfl
  finish := by rw [c.finish, d.finish]

/-- Reversing an edge parameter reverses its two sides, with an orientation-preserving chart. -/
def reverseEdgeChart {V E W I : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype I]
    {J : CopiedGraph V E} {K : CopiedGraph W I}
    (R : Drawing J) (S : Drawing K) (htrace : drawingTrace R = drawingTrace S)
    (e : E) (f : I) (hcurve : ∀ t, R.curve e t = S.curve f (unitInterval.symm t))
    (c : EdgeChart S f) : EdgeChart R e where
  chart := composeOrientedChart c.chart chartHalfTurn
  radius := c.radius
  radius_pos := c.radius_pos
  radius_small := c.radius_small
  straight := by
    intro t ht
    have hs : |(unitInterval.symm t).val - 1/2| < c.radius := by
      change |1 - t.val - 1/2| < c.radius
      have he : 1 - t.val - 1/2 = -(t.val - 1/2) := by ring
      rw [he, abs_neg]
      exact ht
    change chartHalfTurn.map (c.chart.map (R.curve e t)) = _
    rw [hcurve, c.straight _ hs, chart_half_turn_apply]
    apply Prod.ext <;> dsimp <;> ring
  trace_box := by
    intro z hx hy
    have hx' : |(1 - z.1) - 1/2| < c.radius := by
      have he : 1 - z.1 - 1/2 = -(z.1 - 1/2) := by ring
      rw [he, abs_neg]
      exact hx
    have hy' : |(-z.2)| < c.radius := by rw [abs_neg]; exact hy
    change c.chart.map.symm (chartHalfTurn.map.symm z) ∈ drawingTrace R ↔ z.2 = 0
    rw [chart_half_turn_symm_apply, htrace, c.trace_box _ hx' hy']
    exact neg_eq_zero

/-- The complement-component cast exchanges the literal side points for the reversed chart. -/
theorem reverse_edge_chart_faces {V E W I : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype I]
    {J : CopiedGraph V E} {K : CopiedGraph W I}
    (R : Drawing J) (S : Drawing K) (htrace : drawingTrace R = drawingTrace S)
    (e : E) (f : I) (hcurve : ∀ t, R.curve e t = S.curve f (unitInterval.symm t))
    (c : EdgeChart S f) :
    traceFaceEquiv R S htrace (negativeChartFace R e (reverseEdgeChart R S htrace e f hcurve c)) =
      positiveChartFace S f c ∧
    traceFaceEquiv R S htrace (positiveChartFace R e (reverseEdgeChart R S htrace e f hcurve c)) =
      negativeChartFace S f c := by
  have hn : (reverseEdgeChart R S htrace e f hcurve c).chart.map.symm (1/2, -(c.radius/2)) =
      c.chart.map.symm (1/2, c.radius/2) := by
    change c.chart.map.symm (chartHalfTurn.map.symm _) = _
    rw [chart_half_turn_symm_apply]
    congr 1
    apply Prod.ext
    · dsimp; ring
    · simp only [neg_neg]
  have hp : (reverseEdgeChart R S htrace e f hcurve c).chart.map.symm (1/2, c.radius/2) =
      c.chart.map.symm (1/2, -(c.radius/2)) := by
    change c.chart.map.symm (chartHalfTurn.map.symm _) = _
    rw [chart_half_turn_symm_apply]
    congr 1
    apply Prod.ext
    · dsimp; ring
    · rfl
  exact ⟨component_cast_equal _ _ htrace _ _ _ _ hn,
    component_cast_equal _ _ htrace _ _ _ _ hp⟩

end
end FiniteAvalanches.Electrical.SplitStep
