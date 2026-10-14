import FiniteAvalanches.Paper.Revision4498.PastTail
import FiniteAvalanches.Trees.Lattice.PastEscapeLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.CurrentRootConsumers

open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Trees.Lattice.CurrentPastCylinder

/-- The registered box-tail theorem bounds the complementary past cylinder
with the same constant, vertex and window. -/
theorem registered_past_complement_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r M : ℕ, r + 2 ≤ M → ∀ x : Site 2,
      x ∈ boxSites r →
      (squareLatticeUST : Measure EdgeField).real (infinitePastEvent x (boxSites M))ᶜ ≤
        C * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ :=
    FiniteAvalanches.Paper.Revision4498.past_outside_origin_box_bound
  refine ⟨C, hC, ?_⟩
  intro r M hM x hx
  rw [FiniteAvalanches.Paper.CurrentRadiusReduction.infinite_past_compl_real_eq_escape]
  exact htail r M hM x hx

end FiniteAvalanches.Paper.CurrentRootConsumers
