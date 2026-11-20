import FiniteAvalanches.Wilson.Lattice.WiredDualFaceCylinderConvergence
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceLimit

/-! Weak convergence of shifted face-square trees to the wired UST limit. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- The dual face-square tree laws converge weakly to any wired UST limit. -/
theorem wiredDualFaceProbability_tendsto_wiredLimit (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) :
    Tendsto wiredDualFaceProbability atTop (nhds ν) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  apply probabilityMeasure_edgeField_eq_of_cylinder
  intro E p
  obtain ⟨U, hU, hweak⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  have hμc := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak
    (E := cylinder E p) (by rw [(isClopen_cylinder E p).frontier_eq]; exact measure_empty)
  have hfinite := (wiredDualFaceLaw_cylinder_tendsto_wiredLimit ν hν E p).mono_left hU
  exact tendsto_nhds_unique hμc hfinite

/-- Finite complementary-tree bijections imply self-duality of the wired limit. -/
theorem wiredLimit_dual_of_face_tree_equivs (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν))
    (φ : ∀ B, (WiredTrees.graph B).SpanningTree ≃ (wiredDualFaceGraph B).SpanningTree)
    (hφ : ∀ B t, (φ B t).val = t.valᶜ) :
    (ν : Measure EdgeField).map dualField = (ν : Measure EdgeField) :=
  wiredLimit_dual_of_face_limit ν hν (wiredDualFaceProbability_tendsto_wiredLimit ν hν) φ hφ

end
end FiniteAvalanches.Wilson.Lattice
