import FiniteAvalanches.Paper.Revision4498.FiniteApplications

set_option autoImplicit false
namespace FiniteAvalanches.Paper.Revision4498
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory Filter
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Trees.Lattice.PastTail
open FiniteAvalanches.Wilson.Lattice
open scoped Classical BigOperators ENNReal
noncomputable section

theorem wave_counts_eq_core_forward {N : ℕ} (h : Punctured N (origin N)) :
    ∀ x : Site2, waveCounts h.val x = if x ∈ core (forward h).val then 1 else 0 := by
  exact FiniteAvalanches.Paper.Revised.wave_counts_eq_core_forward h

end
end FiniteAvalanches.Paper.Revision4498
