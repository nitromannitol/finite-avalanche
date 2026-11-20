import FiniteAvalanches.Wilson.Lattice.WiredLimitDualTree
import FiniteAvalanches.Trees.Lattice.OneEndSeparation

/-! One tree with one end for weak wired square-lattice UST limits.

Almost surely the primal and dual edge fields are spanning trees
(`wiredLimit_ae_tree_and_dual_tree`), and a spanning lattice tree with connected dual
has exactly one infinite component after every finite deletion
(`existsUnique_infinite_componentCompl_of_dual_connected`). -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice

noncomputable section

/-- Every weak wired UST limit is supported on spanning trees of `ℤ²` that have exactly
one infinite component after every finite deletion. -/
theorem wiredLimit_ae_tree_and_existsUnique_infinite_componentCompl
    (ν : ProbabilityMeasure EdgeField) (hν : Tendsto finiteProbability atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), IsTree ω ∧
      ∀ K : Finset (Site 2),
        ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)),
          (SimpleGraph.ComponentCompl.supp C).Infinite := by
  filter_upwards [wiredLimit_ae_tree_and_dual_tree ν hν] with ω hω
  exact ⟨hω.1, fun K =>
    existsUnique_infinite_componentCompl_of_dual_connected ω hω.1 hω.2.connected K⟩

end
end FiniteAvalanches.Wilson.Lattice
