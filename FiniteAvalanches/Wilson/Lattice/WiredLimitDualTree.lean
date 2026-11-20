import FiniteAvalanches.Wilson.Lattice.WiredLimitConnected
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceCutParity
import FiniteAvalanches.Trees.Lattice.EuclideanPaths

/-! Primal and dual connectivity of weak wired square-lattice UST limits. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Every weak wired UST limit is supported on fields whose primal and dual
are both spanning trees. -/
theorem wiredLimit_ae_tree_and_dual_tree (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), IsTree ω ∧ IsTree (dualField ω) := by
  have htree := wiredLimit_ae_tree ν hν
  have hmap : ∀ᵐ ω ∂((ν : Measure EdgeField).map dualField), IsTree ω := by
    rw [wiredLimit_self_dual ν hν]
    exact htree
  have hdual : ∀ᵐ ω ∂(ν : Measure EdgeField), IsTree (dualField ω) :=
    (ae_map_iff measurable_dualField.aemeasurable BarlowMasson.measurableSet_isTree).mp hmap
  filter_upwards [htree, hdual] with ω hp hd
  exact ⟨hp, hd⟩

end
end FiniteAvalanches.Wilson.Lattice
