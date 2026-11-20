import FiniteAvalanches.Wilson.Lattice.FreeCylinderConvergence
import FiniteAvalanches.Wilson.Lattice.FiniteUstWeakLimit

/-! Weak convergence of free-box spanning trees to the wired limit. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Free square-box UST laws converge weakly to every weak wired UST limit. -/
theorem freeBoxProbability_tendsto_wiredLimit (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) :
    Tendsto freeBoxProbability atTop (nhds ν) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  apply probabilityMeasure_edgeField_eq_of_cylinder
  intro E p
  obtain ⟨U, hU, hweak⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  have hμc := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak
    (E := cylinder E p) (by rw [(isClopen_cylinder E p).frontier_eq]; exact measure_empty)
  have hfinite := (freeBoxLaw_cylinder_tendsto_wiredLimit ν hν E p).mono_left hU
  exact tendsto_nhds_unique hμc hfinite

end
end FiniteAvalanches.Wilson.Lattice
