import FiniteAvalanches.Wilson.Lattice.CurrentForestReciprocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.CurrentSource
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

theorem forest_reciprocal_cofinite :
    ∃ a C : ℝ, 0 < a ∧ ∀ K : Finset (Site 2),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      ∀ γ : Set (Site 2), ((lattice 2).induce γ).Connected → γᶜ.Finite →
        Disjoint (K : Set (Site 2)) γ →
        (∃ k ∈ K, ∃ y ∈ γ, (lattice 2).Adj k y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
        (∫ σ, (1 : ℝ) / (contacts K σ : ℝ) ∂wilsonColorLaw R) ≤
          C * Real.rpow (Real.log (((K.sup (fun x => K.sup (fun y => siteRadius x y)) : ℕ) : ℝ) + 2)) (-a) := by
  exact FiniteAvalanches.Wilson.Lattice.CurrentForestReciprocal.forest_reciprocal_cofinite_current

end
end FiniteAvalanches.Paper.CurrentSource
