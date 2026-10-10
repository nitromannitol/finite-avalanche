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

theorem past_outside_origin_box_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r M : ℕ, r + 2 ≤ M → ∀ x : Site2,
      x ∈ boxSites r →
      (squareLatticeUST : Measure EdgeField).real
        {ω | ∃ hT : IsTree ω, ∃ hOne : OneEnded ω,
          ¬vertexPast ω hT hOne x ⊆ (boxSites M : Set Site2)} ≤
        C * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  exact FiniteAvalanches.Paper.Revised.past_outside_origin_box_bound

end
end FiniteAvalanches.Paper.Revision4498
