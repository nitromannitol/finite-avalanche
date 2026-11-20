import FiniteAvalanches.Support.Plane.CrossingBoundaryAccess

/-!
# Chart parametrization of crossing access paths

An access path that follows a crossing stub near its endpoint has the exact
standard chart parametrization near the crossing.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set unitInterval Source BSST

/-- A parametrized terminal stub yields the standard local crossing speed. -/
theorem crossing_stub_terminal_chart {X : Type*} [TopologicalSpace X]
    {x : X} (q : unitInterval → X) (hq : Continuous q) (side : Bool)
    (p : Path x (q ⟨1 / 2, by norm_num⟩)) (u : unitInterval) (hu : u ≠ 1)
    (htail : ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
      p t = midpointStub q hq side ⟨2 * (t : ℝ) - 1, by
        constructor
        · have := u.property.1
          linarith
        · linarith [t.property.2]⟩)
    (chart : X → ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (hchart : ∀ t : unitInterval, |(t : ℝ) - 1 / 2| < r / 2 →
      chart (q t) = (1 / 2, (t : ℝ) - 1 / 2)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : unitInterval, 1 - 2 * δ < (t : ℝ) →
      chart (p t) = if side then (1 / 2, (1 - (t : ℝ)) / 2)
        else (1 / 2, ((t : ℝ) - 1) / 2) := by
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2
    (fun h => hu (Subtype.ext h))
  let δ : ℝ := min (r / 4) ((1 - (u : ℝ)) / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hδu : δ ≤ (1 - (u : ℝ)) / 4 := min_le_right _ _
  have hδr : δ ≤ r / 4 := min_le_left _ _
  have ht' : ((u : ℝ) + 1) / 2 ≤ t := by linarith
  rw [htail t ht']
  let v : unitInterval := ⟨2 * (t : ℝ) - 1, by
    constructor
    · have := u.property.1
      linarith
    · linarith [t.property.2]⟩
  change chart (q (crossingStubParameter side v)) = _
  have hv : (v : ℝ) = 2 * (t : ℝ) - 1 := rfl
  have hdist : |(crossingStubParameter side v : ℝ) - 1 / 2| < r / 2 := by
    cases side with
    | false =>
        simp only [crossingStubParameter, Bool.false_eq_true, ↓reduceIte]
        rw [abs_of_nonpos (by linarith [t.property.2])]
        linarith
    | true =>
        simp only [crossingStubParameter, ↓reduceIte]
        rw [abs_of_nonneg (by linarith [t.property.2])]
        linarith
  rw [hchart _ hdist]
  cases side <;> simp only [crossingStubParameter, Bool.false_eq_true, ↓reduceIte]
  all_goals congr 1; linarith

end FiniteAvalanches.Electrical.StatementGeometry
