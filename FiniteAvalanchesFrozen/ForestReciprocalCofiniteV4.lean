import FiniteAvalanchesProofs.ForestReciprocalCofiniteV4
import FiniteAvalanches.Wilson.Lattice.Law
import FiniteAvalanches.Wilson.Lattice.ForestEvents
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.SourceTargets
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

theorem forest_reciprocal_cofinite_v4 :
    ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
    ((lattice 2).induce (K : Set (Site 2))).Connected →
    ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected →
      γᶜ.Finite → Disjoint (K : Set (Site 2)) γ →
      (∃ k ∈ K, ∃ y ∈ γ, (lattice 2).Adj k y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
        (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
          C * Real.rpow
            (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2))
            (-a) := by
  exact FiniteAvalanchesProofs.ForestReciprocalCofiniteV4.forest_reciprocal_cofinite_v4

end
end FiniteAvalanches.Wilson.Lattice.SourceTargets
