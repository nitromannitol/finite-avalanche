import FiniteAvalanches.Wilson.Lattice.LocalComparison.CurrentComparison
import CurrentSource.ReferenceMomentCurrent

set_option autoImplicit false
namespace CurrentLocalComparison
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice MeasureTheory
open scoped Classical
noncomputable section

/-- The one-scale local comparison with a uniform positive probability. -/
theorem current_local_comparison :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℕ) (_hr : 10^30 ≤ r) (R : RootPair)
      (_hcofinite : (R.zero ∪ R.one)ᶜ.Finite)
      (_h0 : (0 : Site 2) ∈ R.zero)
      (_hneigh : ∃ b ∈ R.one, (lattice 2).Adj 0 b)
      (_hZero : ((lattice 2).induce R.zero).Connected)
      (_hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
      (_hOne : ((lattice 2).induce R.one).Connected)
      (_hmeet : ∃ y ∈ R.one, siteRadius 0 y = r),
      ε ≤ (wilsonColorLaw R).real
        (localContactEvent R.zero 0 (2*r) (Real.log (r : ℝ)/8)) := by
  exact conditional_local_comparison
    FiniteAvalanches.Electrical.Source.Reference.reference_moment_current

end
end CurrentLocalComparison
