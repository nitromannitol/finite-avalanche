import FiniteAvalanches.Wilson.Lattice.WiredDualFaceObservations
import FiniteAvalanches.Wilson.Lattice.FreeWeakLimit

/-! Reduction of infinite self-duality to finite tree complementation and the
shifted free-box limit. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- A complementary finite-tree bijection and convergence of the dual face
square laws imply self-duality of the wired limit. -/
theorem wiredLimit_dual_of_face_limit (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν))
    (hface : Tendsto wiredDualFaceProbability atTop (nhds ν))
    (φ : ∀ B, (WiredTrees.graph B).SpanningTree ≃ (wiredDualFaceGraph B).SpanningTree)
    (hφ : ∀ B t, (φ B t).val = t.valᶜ) :
    (ν : Measure EdgeField).map dualField = (ν : Measure EdgeField) := by
  apply wiredLimit_dual_of_cylinder_limits ν hν
  intro E p
  have hmass := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hface (E := cylinder E p) (by
      rw [(isClopen_cylinder E p).frontier_eq]
      exact measure_empty)
  have heq := eventually_finite_dual_cylinder_eq_dualFaceLaw φ hφ E p
  have hpre : ∀ᶠ B : ℕ in atTop,
      finiteLaw B (cylinder (crossingEdges E) (crossingPattern E p)) =
        wiredDualFaceLaw B (cylinder E p) := by
    filter_upwards [heq] with B hB
    rw [← dualField_preimage_cylinder]
    exact hB
  exact hmass.congr' (hpre.mono (fun _ h => h.symm))

end
end FiniteAvalanches.Wilson.Lattice
