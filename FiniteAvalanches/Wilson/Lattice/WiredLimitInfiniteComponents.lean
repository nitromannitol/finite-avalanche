import FiniteAvalanches.Wilson.Lattice.WiredLimitDualTree

/-! Infinite components after finite deletions in wired UST limits. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Every finite vertex deletion from a spanning lattice tree leaves at least
one infinite component. -/
theorem tree_exists_infinite_componentCompl (ω : EdgeField) (hT : IsTree ω)
    (K : Finset (Site 2)) :
    ∃ C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite := by
  haveI : Fact (toGraph ω).Preconnected := ⟨hT.connected.preconnected⟩
  obtain ⟨e, he⟩ := SimpleGraph.nonempty_ends_of_infinite (toGraph ω)
  exact ⟨e (Opposite.op K),
    SimpleGraph.end_componentCompl_infinite (toGraph ω) ⟨e, he⟩ (Opposite.op K)⟩

/-- Every finite vertex deletion has an infinite component almost surely for a
weak wired UST limit. -/
theorem wiredLimit_ae_exists_infinite_componentCompl (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), ∀ K : Finset (Site 2),
      ∃ C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite := by
  filter_upwards [wiredLimit_ae_tree ν hν] with ω hT K
  exact tree_exists_infinite_componentCompl ω hT K

end
end FiniteAvalanches.Wilson.Lattice
